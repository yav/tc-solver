{- |
The purpose of the solver is to turn an arbitrary set of propositions
into an inert one.  This is done by starting with some inert set
(e.g., the empty set of propositions) and then adding each new proposition
one at a time.  Assumptions and goals are added in different ways, so
we have two different functions to add a proposition to an existing
inert set.
-}

module TcTypeNats
  ( SolverS(..)
  , initSolverS
  , addWorkItemsM
  , Inerts(..)
  ) where

import TcTypeNatsBase
import TcTypeNatsProps as Props
import TcTypeNatsEq as Subst
import TcTypeNatsLeq
import TcTypeNatsFacts
import TcTypeNatsRules
import TcTypeNatsEval

import Debug.Trace
import Text.PrettyPrint
import Data.Maybe(fromMaybe,isNothing)
import Data.List(find)
import Control.Monad(MonadPlus(..),msum,foldM)

data SolverS = SolverS
  { ssTodoFacts :: Props Fact
  , ssTodoGoals :: [Goal]
  , ssSolved    :: [(EvVar,Proof)]
  , ssInerts    :: Inerts
  }


{-|
The inert set is a collection of propositions, which keeps track
of the facts that are known by the solver, as well as any goals that
were attempted but not solved.  We refer to this set as ``inert'' because
the propositions in it cannot ``interact'' with each other. -}
data Inerts = Inerts { given :: Facts, wanted :: Props Goal }

noInerts :: Inerts
noInerts = Inerts { given = noFacts, wanted = Props.empty }

instance PP Inerts where
  pp is = pp (given is) $$ pp (wanted is)



initSolverS :: SolverS
initSolverS = SolverS
  { ssTodoGoals = []
  , ssTodoFacts = Props.empty
  , ssSolved    = []
  , ssInerts    = noInerts
  }


-- | The final state should have empty 'todo*' queues.
addWorkItemsM :: SolverS -> TCN SolverS

addWorkItemsM ss0 =
  case getFact ss0 of
    Just (fact, ss1) ->
      do r <- addGiven fact (ssInerts ss1)
         addWorkItemsM (nextState r ss1)

    Nothing ->
      case getGoal ss0 of
       Just (goal, ss1) ->
         do r <- addWanted goal (ssInerts ss1)
            addWorkItemsM (nextState r ss1)

       Nothing -> return ss0




{- | When processing facts, it is more
efficient if we first process equalities, then order and, finally, all other
facts.  To make this easy, we store unprocessed facts as 'Prpos' instead
of just using a list.

We add equalities first because they might lead to improvements that,
in turn, would enable the discovery of additional facts.  In particular, if a
presently known fact gets improved, then the old fact is removed from the
list of known facts, and its improved version is added as new work.  Thus,
if we process equalities first, we don't need to do any of this "restarting".

For similar reasons we process ordering predicates before others: they
make it possible for certain conditional rules to fire.  For example,
the cancellation rule for multiplication requires that the argument that
is being cancelled is greater than 0.
-}

getFact :: SolverS -> Maybe (Fact, SolverS)
getFact s = case getOne (ssTodoFacts s) of
              Nothing     -> Nothing
              Just (f,fs) -> Just (f, s { ssTodoFacts = fs })

getGoal :: SolverS -> Maybe (Goal, SolverS)
getGoal s = case ssTodoGoals s of
              []     -> Nothing
              g : gs -> Just (g, s { ssTodoGoals = gs })

nextState :: PassResult -> SolverS -> SolverS
nextState r s =
  SolverS { ssTodoFacts = Props.union (newFacts r) (ssTodoFacts s)
          , ssTodoGoals = newGoals r ++ ssTodoGoals s
          , ssInerts    = newInerts r
          , ssSolved    = solvedWanted r ++ ssSolved s
          }

--------------------------------------------------------------------------------



data PassResult = PassResult { solvedWanted :: [(EvVar,Proof)]
                             , newGoals     :: [Goal]
                             , newFacts     :: Props Fact
                             , newInerts    :: Inerts
                             }

noChanges :: Inerts -> PassResult
noChanges is = PassResult { solvedWanted = []
                          , newGoals     = []
                          , newFacts     = Props.empty
                          , newInerts    = is
                          }


--------------------------------------------------------------------------------


{-| Adding a new assumptions to an inert set.
If the assumptions was added to the set, then we remove any existing goals
and add them as new work, in case they can be solved in terms of the
new fact. -}
addGiven  :: Fact -> Inerts -> TCN PassResult
addGiven g props =
  case addFact g (given props) of
    Inconsistent  -> mzero
    AlreadyKnown  -> return (noChanges props)
    Improved fact -> return (noChanges props)
                            { newFacts = Props.singleton fact }
    Added new newProps -> return
      PassResult { newGoals      = Props.toList (wanted props)
                 , newFacts      = new
                 , solvedWanted  = []
                 , newInerts     = Inerts { given  = newProps
                                          , wanted = Props.empty
                                          }
                 }



{- 'addFact' attempts to extend a collection of already known facts.
The resulting value contains information about how the new fact
interacted with the already existing facts.

Note that adding a fact may result in removing some existing facts from
the set (e.g., if they become obsolete in the presence of the new fact).
It is quite common to add a fact and "reprocess" a bunch of existing
facts by removing them from the set and adding improved version as
new work.
-}

data AddFact = Inconsistent
             | AlreadyKnown
             | Improved Fact
             | Added (Props Fact) Facts     -- additional facts, new set

addFact :: Fact -> Facts -> AddFact
addFact f fs =
  case impFactMb (factsEq fs) f of
    Just f1 -> Improved f1
    Nothing ->
      case factProp f of
        Prop Eq  [s,t] -> eqAddFact  (factProof f) s t fs
        Prop Leq [s,t] -> leqAddFact (factProof f) s t fs
        _ | impossible (factProp f) -> Inconsistent
        _ ->
          case solve (facts fs) (factProp f) of
            Just _ -> AlreadyKnown

            -- XXX: Modify "implied" to generate Props directly.
            _      -> Added (Props.fromList (implied fs f))
                            fs { facts = Props.insert f (facts fs) }
  where
  -- XXX: It would be nicer to make this less ad-hoc.
  impossible (Prop Mul [Num x _, _, Num y _]) = isNothing (divide y x)
  impossible (Prop Exp [Num x _, _, Num y _]) = isNothing (descreteLog y x)
  impossible (Prop Exp [_, Num x _, Num y _]) = isNothing (descreteRoot y x)
  impossible _ = False


eqAddFact :: Proof -> Term -> Term -> Facts -> AddFact
eqAddFact eq t1 t2 fs =
  case (t1, t2) of
    _ | t1 == t2      -> AlreadyKnown

    (Num {}, Num {})  -> Inconsistent

    (Var x, Num {})   -> eqBindVar eq x t2 fs

    (Var x, _)
      | not (leqContains (factsLeq fs) t1) -> eqBindVar eq x t2 fs

    (_, Var y)        -> eqBindVar (bySym t1 t2 eq) y t1 fs


eqBindVar :: Proof -> Var -> Term -> Facts -> AddFact
eqBindVar eq x t fs = Added (Props.fromList (leqRestart ++ changed))
                            Facts { factsEq   = compose su (factsEq fs)
                                  , factsLeq  = leqModel
                                  , facts     = others
                                  }

  where
  {-No need for an "occurs" check because the terms are simple (no recursion)-}
  su                     = Subst.singleton eq x t

  (leqRestart, leqModel) = case leqExtract (Var x) (factsLeq fs) of
                             Nothing      -> ([], factsLeq fs)
                             Just (lfs,m) -> (map (impFact su) lfs, m)

  (changed, others)      = Props.mapExtract (impFactMb su) (facts fs)

leqAddFact :: Proof -> Term -> Term -> Facts -> AddFact
leqAddFact proof t1 t2 fs =
  let m0        = factsLeq fs
      (n1,m1)   = leqInsNode t1 m0
      (n2,m2)   = leqInsNode t2 m1

  in case leqReachable m2 t2 t1 of

       Nothing ->

         case leqReachable m2 t1 t2 of
           Nothing -> let (_,_,m3) = leqLink proof (t1,n1) (t2,n2) m2
                      in Added (facts fs)
                               fs { factsLeq = m3, facts = Props.empty }
           Just _  -> AlreadyKnown

       {- We know the opposite: we don't add the fact
          but propose an equality instead. -}
       Just pOp -> Improved $
         Fact { factProof = byLeqAsym t1 t2 proof pOp
              , factProp  = Prop Eq [t1,t2]
              }



{-------------------------------------------------------------------------------
Using Existing Goals
-------------------------------------------------------------------------------}

assumeGoals :: MonadPlus m => [Goal] -> Facts -> m Facts
assumeGoals as bs = maybe mzero return
                  $ addFactsTrans bs
                  $ Props.fromList
                  $ map goalToFact as

{- The function 'goalToFact' is used when we attempt to solve a new goal
in terms of already existing goals. -}
goalToFact :: Goal -> Fact
goalToFact g = Fact { factProof = ByAsmp (goalName g), factProp = goalProp g }


{- Add a fact and all the facts that follow from it.  The arguments are
ordered like this so that the function can be used conveniently with 'foldM'. -}

addFactTrans :: Facts -> Fact -> Maybe Facts
addFactTrans facts0  fact =
  case addFact fact facts0 of
    Inconsistent    -> mzero
    AlreadyKnown    -> return facts0
    Improved fact1  -> addFactTrans  facts0 fact1
    Added fs facts1 -> addFactsTrans' facts1 fs


{- Add a collection of facts and all the facts that follow from them.
We add equalities first, because they might lead to improvements that,
in turn, would enable the discovery of additional facts.
Furthermore, improvements "restart" so we do less work if we do equalities
first. -}

addFactsTrans' :: Facts -> Props Fact -> Maybe Facts
addFactsTrans' fs = foldM addFactTrans fs . Props.toList

addFactsTrans :: Facts -> Props Fact -> Maybe Facts
addFactsTrans fs facts0 =
  trace "Transitive facts" $
  case addFactsTrans' fs facts0 of
    Nothing -> trace "(nothing)" Nothing
    Just x  -> trace (show (pp x)) $ Just x



{-------------------------------------------------------------------------------
Results of Entailement
-------------------------------------------------------------------------------}

{- | The entailment function may return one of three possible answers,
informally corresponding to ``certainly not'', ''not in its current form'',
and ''(a qualified) yes''. -}
data Answer = NotForAny | NotForAll | YesIf [Goal] Proof


{- More precisely, \Verb"NotForAny" asserts that the proposition in question
contradicts the given set of assumptions, no matter how we instantiate its
free variables (i.e., we have a proof of the proposition's negation).
The following two examples both result in a \Verb"NotForAny" answer
(in the examples we use the more traditional mathematical notation
$ps \ent p$ for entailment)
$$
\begin{aligned}
      & \ent 2 + 3 = 6 &\mapsto~\mathtt{NotForAny}\\
x = 2 & \ent x = 3     &\mapsto~\mathtt{NotForAny}
\end{aligned}
$$
The first equation is is inconsistent with the theory in general, while the
second contradicts a particular assumption.

If the entailment function returns \Verb"NotForAll", then the proposition in
question is not entailed by the given assumptions but it also does not
contradict them.  Typically this happens when a proposition contains
free variables, and the entailment of the proposition depends on how
these variables are instantiated (e.g., some instantiations result in
propositions that are consistent with the assumptions, while others do not).
For example, consider the following entailment question:
$$
\begin{aligned}
& \ent x + y = 6     &\mapsto~\mathtt{NotForAll}
\end{aligned}
$$
This results in \Verb"NotForAll" because we cannot determine if the
proposition holds without further assumptions about $x$ and $y$---%
some instantiations (e.g., $x = 2, y = 4$)
are entailed, while others (e.g., $x = 7, y = 3$) are not.

Finally, the entailment function may give a positive answer, with an optional
list of sub-goals.  Consider the following examples:
$$
\begin{aligned}
& \ent 1 + 2 = 3 &&\mapsto~\mathtt{YesIf~[]} \\
& \ent x + 0 = x &&\mapsto~\mathtt{YesIf~[]} \\
& \ent 3 + 5 = x &&\mapsto~\mathtt{YesIf~[x=8]}
\end{aligned}
$$
The first two examples illustrate unconditional entailment, while the third
example asserts that the proposition is entailed if and only if $x = 8$ holds.
The sub-goals contained in a \Verb"YesIf" answer should be logically
equivalent to the original goal (under the given assumptions) but also
``simpler'', a concept that we shall discuss further in
Section~\ref{sec_improvement}.  -}



{-------------------------------------------------------------------------------
Adding a New Goal (wanted)

Extending the inert set with a new goal is a little more complex then
adding a new assumption but the overall structure of the algorithm is similar.
Again, we use the entailment function to check for interactions
between the inert set and the new goal but we also use existing goals
as assumptions.  This is useful because we may be able to discharge
the new goal in terms of already existing goals, thus leaving the inert
set unchanged.
-------------------------------------------------------------------------------}

addWanted :: Goal -> Inerts -> TCN PassResult
addWanted w props =

     do asmps <- assumeGoals wantedList (given props)
        res <- entails asmps w
        case res of

{- The first two cases---when there is interaction---are the same as for
adding an assumption:  inconsistencies result in an error, while solving
the new goal does not affect the inert set but may add a new formulation
of the goal to the work queue. -}

          NotForAny -> mzero

          YesIf ps proof -> return PassResult
            { solvedWanted  = [ (goalName w, proof) ]
            , newGoals      = ps
            , newFacts      = Props.empty
            , newInerts     = props
            }

{- The major difference in the algorithm is when there is no interaction
between the new goal and the existing inert set.  In this case we
add the new goal to the inert set but, in addition, we need to check
if it is possible to solve any of the already existing goals in terms
of the new goal.  We cannot simply add the existing goals back on the
work queue because this may lead to a non-terminating loop:
any two goals that cannot be solved in terms
of each other are going to keep restarting each other forever.  Instead,
we examine the existing goals one at a time and check for interactions in
the presence of the new goal, removing goals that are entailed, and leaving
goals that result in no interaction in the inert set. -}

          NotForAll ->
                do asmps0 <- assumeGoals [w] (given props)
                   (solved,new) <- checkExisting [] [] asmps0 wantedList
                   let keepGoal p = not (goalName p `elem` map fst solved)

                   return PassResult
                     { solvedWanted = solved
                     , newGoals     = new
                     , newFacts     = Props.empty
                     , newInerts =
                        props { wanted = Props.insert w
                                         (Props.filter keepGoal (wanted props)) }
                     }

  where
  wantedList        = Props.toList (wanted props)

{- The function 'checkExisting' has the details of how to check for interaction
between some existing goal, 'w1', and the new goal 'w'.  The function uses
four pieces of state:

  * 'solved' is a list which accumulates existing goals that were solved,

  * 'new' is a collection of newly generated goals---these may arise when
    we solve an existing goal, but the proof needs some new sub-goals,

  * 'asmps' is the collection of facts that we know about---this is a mixture
    of the original facts and goals that we tried to solve but failed,

  * 'ws' is a collection of goals that we still need to examine.
-}

  checkExisting solved new asmps ws =
    case ws of
      [] -> return (solved, new)
      w1 : ws1 ->
        do asmps1 <- assumeGoals ws1 asmps
           res <- entails asmps1 w1
           case res of
             NotForAny -> mzero
             NotForAll ->
               do asmps2 <- assumeGoals [w1] asmps
                  checkExisting solved new asmps2 ws1
             YesIf ps proof ->
               do asmps2 <- assumeGoals ps asmps
                  checkExisting ((goalName w1, proof) : solved)
                                (ps ++ new)
                                asmps2
                                ws1



{- To see the algorithm in action, consider the following example:

New goal:   2 <= x
Inert set:  { wanted = [x + 5 = y, 1 <= x] }

Step 1: entails [x + 5 = y, 1 <= x] (2 <= x)      -->  NotForAll
Step 2: Add (2 <= x) to the inert set and examine existing goals:
  Step 2.2: entails [2 <= x, 1 <= x] (x + 5 = y)  --> NotForAll // keep
  Step 2.1: entails [2 <= x, x + 5 = y] (1 <= x)  --> YesIf []  // remove

New inert set: { wanted = [2 <= x, x + 5 = y] }

-}


{-------------------------------------------------------------------------------
Entailment

A central component of the solver is the entailment function, which determines
if a set of assumptions (the first argument), entail a certain proposition
(the second argument).
-------------------------------------------------------------------------------}


entailsSimple :: Facts -> Goal -> TCN Answer
entailsSimple ps p =
  do improved <- impGoal (factsEq ps) p
     return $ fromMaybe NotForAll
            $ msum [ do (p1,proof) <- improved
                        return (YesIf [p1] proof)

                   , do proof <- case goalProp p of
                                   Prop Leq [s,t] -> leqProve (factsLeq ps) s t
                                   g -> solve (facts ps) g
                        return (YesIf [] proof)
                   ]

entails :: Facts -> Goal -> TCN Answer

-- For debugging.
entails ps p | gTrace msg = undefined
  where msg = text "Entails?" $$ nest 2 (vcat (map pp (Props.toList (facts ps)))
                                      $$ text "-----------------"
                                      $$ pp p
                                        )

entails ps p =
  do attempt1 <- entailsSimple ps p
     case attempt1 of
       NotForAll
         | improvable ->    -- Is there room for improvement?
         case assumeGoals [p] ps of

           -- The new goal contradicts the given assumptions.
           Nothing -> return NotForAny

           {- New facts!  We consider only the equalities. -}
           Just (Facts { factsEq = su1 }) ->
             do eqns <- mapM newGoal $ map factProp $ Subst.toFacts su1
                case assumeGoals eqns ps of
                  Nothing  -> return NotForAny
                  Just ps1 ->
                    do ans <- entailsSimple ps1 p
                       case ans of
                         YesIf qs proof -> return (YesIf (eqns ++ qs) proof)
                         _              -> return ans

       _ -> return attempt1

  where improvable = case goalProp p of
                       Prop Eq _ -> False -- Already an equality, leave it be.
                       _         -> True


{- Note A: We try improvement proper.  This means that we
need to find a logically equivalent set of goals that might lead to progress.

The new goals needs to imply the original to preserve soundness (i.e.,
we don't just loose goals).  Also, the original goal needs to imply the new
set to preserve completeness (i.e., we don't make the program harder and so
reject valid programs).

The improvement process starts by adding the goal as a new assumption
to the existing set of facts, then computing what new facts follow from this.
These new facts are candiadtes for replacing the goal because they satisfy
the completenss side of the double implication.  The proofs of these facts
are discarded because they use the original goal as an assumption---we are
interested only in the computed propositions.

Next, we filter out propositions that are cosidered to be more complex than
the current goal, according to some metric.  At present, we consider
only new equality constraints so, essentially, we are computing an improving
substitution.  This provides goals that, potentially, could be of interest
to other passes of GHC's constraint solver.

Finally, we check if we can solve the original goal by using the new
proposiitons as assumptions, and if so we have found an improving
substitution.
-}



newGoal :: Prop -> TCN Goal
newGoal p =
  do x <- newEvVar
     return Goal { goalName = x, goalProp = p }

{- Given a goal, return a new goal, and a proof which
solves the old goal in terms of the new one.
We return 'Nothing' if nothing got improved. -}
impGoal :: Subst -> Goal -> TCN (Maybe (Goal, Proof))
impGoal su p
  | Subst.isIdentity su || propArgs p == ts  = return Nothing
  | otherwise = do g <- newGoal (Prop (propPred p) ts)
                   return $ Just (g, byCong (propPred p)
                                       (ts ++ propArgs p)
                                       (zipWith3 bySym (propArgs p) ts evs)
                                       (ByAsmp (goalName g)))
  where (evs,ts) = unzip $ map (Subst.apply su) (propArgs p)

-- If "A : P x", and "B : x = 3", then "ByCong P [B] A : P 3"
impFact :: Subst -> Fact -> Fact
impFact su p = fst (impFactChange su p)

impFactMb :: Subst -> Fact -> Maybe Fact
impFactMb su p = case impFactChange su p of
                   (_,False)  -> Nothing
                   (fact1,_)  -> Just fact1

-- If "A : P x", and "B : x = 3", then "ByCong P [B] A : P 3"
impFactChange :: Subst -> Fact -> (Fact, Bool)
impFactChange su p = ( p { factProof = byCong (propPred p) (propArgs p ++ ts)
                                                           evs (factProof p)
                         , factProp  = Prop (propPred p) ts
                         }

                     -- Indicates if something changed.
                     , not (all isRefl evs)
                     )
  where (evs,ts) = unzip $ map (Subst.apply su) (propArgs p)


--------------------------------------------------------------------------------

solve :: Props Fact -> Prop -> Maybe Proof
solve  _ (Prop Eq [x,y]) | x == y = Just (byRefl x)
solve ps p = solve0 [] p `mplus` byAsmp ps p

byAsmp :: Props Fact -> Prop -> Maybe Proof
byAsmp ps p =
  do q <- find (\x -> propArgs x == propArgs p) $ getPropsFor (propPred p) ps
     return (factProof q)





{-------------------------------------------------------------------------------
Misc.
-------------------------------------------------------------------------------}

ppTrace :: Doc -> a -> a
ppTrace d = trace (show d)

gTrace :: Doc -> Bool
gTrace d = ppTrace d False



