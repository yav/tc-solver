{-|
The inert set is a collection of propositions, which keeps track
of the facts that are known, as well as any goals that
were attempted but not solved.  We refer to this set as ``inert'' because
the propositions in it cannot ``interact'' with each other.
-}

module TcTypeNats
  ( Inerts(..)
  , noInerts
  , insertFact
  , insertGoal
  , InsertInert(..)
  ) where

import           TcTypeNatsBase
import           TcTypeNatsProps  as Props
import           TcTypeNatsEq     as Subst
import qualified TcTypeNatsLeq    as Leq
import           TcTypeNatsFacts  as Facts
import           TcTypeNatsRules
import           TcTypeNatsEval

import Debug.Trace
import Text.PrettyPrint
import Data.Maybe(fromMaybe,isNothing)
import Data.List(find)
import Control.Monad(MonadPlus(..),msum)

-- | An colection of a facts and goals that cannot interact with each other.
data Inerts = Inerts { facts :: Facts, goals :: Props Goal }

-- | The empty inert collection.
noInerts :: Inerts
noInerts = Inerts { facts = Facts.empty, goals = Props.empty }

instance PP Inerts where
  pp is = pp (facts is) $$ pp (goals is)



-- | The result of trying to insert a new goal or fact to an inert set.
data InsertInert = InsertInert
  { solvedGoals  :: [(EvVar,Proof)]   -- ^ Goals that were proved.
  , newGoals     :: [Goal]            -- ^ New goals that need proof.
  , newFacts     :: Props Fact        -- ^ New facts that need proof.
  , newInerts    :: Inerts            -- ^ The new inert set.
  }

noChanges :: Inerts -> InsertInert
noChanges is = InsertInert { solvedGoals = []
                           , newGoals     = []
                           , newFacts     = Props.empty
                           , newInerts    = is
                           }


-- Facts -----------------------------------------------------------------------


{-| Adding a new assumptions to an inert set.
If the assumptions was added to the set, then we remove any existing goals
and add them as new work, in case they can be solved in terms of the
new fact. -}
insertFact  :: Fact -> Inerts -> TCN InsertInert
insertFact g props =
  case addFact g (facts props) of
    Inconsistent  -> mzero
    AlreadyKnown  -> return (noChanges props)
    Improved f    -> return (noChanges props) { newFacts = Props.singleton f }

    -- XXX: Should export equalities, in case ither solvers are interested
    Added new newProps ->
      case addFactsTrans newProps new of
        Nothing -> mzero
        Just fs -> return
          InsertInert { newGoals     = Props.toList (goals props)
                      , newFacts     = Props.empty
                      , solvedGoals  = []
                      , newInerts    = Inerts { facts  = fs
                                              , goals  = Props.empty
                                              }
                      }
    


{-| Try to extend a collection of already known facts.

Note that adding a fact may result in removing some existing facts from
the set (e.g., if they become obsolete in the presence of the new fact).
It is quite common to add a fact and "reprocess" a bunch of existing
facts by removing them from the set and adding improved version as
new work.
-}

addFact :: Fact -> Facts -> AddFact
addFact f fs
  -- | gTrace (text "adding fact:" <+> pp f) = undefined
  | otherwise =
  case improveFact (getEqFacts fs) f of
    Just f1 -> Improved f1
    Nothing ->
      case factProp f of
        _ | impossible (factProp f) -> Inconsistent

        Prop Eq  [s,t] -> addEqFact  (factProof f) s t fs
        Prop Leq [s,t] -> addLeqFact (factProof f) s t fs

        _ ->
          case solve (getOtherFacts fs) (factProp f) of
            Just _ -> AlreadyKnown

            -- XXX: Modify "implied" to generate Props directly.
            _      -> let new = addOtherInertFact f fs
                          imp = Props.fromList (implied new (propPred f))
                          -- dbg = vcat [ pp (factProp f) <+> pp (factProof f) | f <- Props.toList imp ]
                      in Added imp new


-- Using Existing Goals --------------------------------------------------------

assumeGoals :: MonadPlus m => [Goal] -> Facts -> m Facts
assumeGoals as bs = maybe mzero return
                  $ addFactsTrans bs
                  $ Props.fromList
                  $ map goalToFact as

{- The function 'goalToFact' is used when we attempt to solve a new goal
in terms of already existing goals. -}
goalToFact :: Goal -> Fact
goalToFact g = Fact { factProof = ByAsmp (goalName g), factProp = goalProp g }


{- Add a collection of facts and all the facts that follow from them.
We add equalities first, because they might lead to improvements that,
in turn, would enable the discovery of additional facts.
Furthermore, improvements "restart" so we do less work if we do equalities
first. -}

addFactsTrans :: Facts -> Props Fact -> Maybe Facts
addFactsTrans fs0 todo = withFacts todo fs0 [] [] ([],[])
  where
  withFacts work fs eqs leqs (hd,tl) =
    loop fs (Props.getPropsFor Eq work ++ eqs)
            (Props.getPropsFor Leq work ++ leqs)
            (hd, Prelude.filter isOther (Props.toList work) : tl)

  loop fs (eq:eqs) leqs   others      = add1 eq fs eqs leqs others
  loop fs [] (leq : leqs) others      = add1 leq fs [] leqs others
  loop fs [] [] ((f : more) : hd, tl) = add1 f   fs [] []   (more : hd, tl)
  loop fs [] [] ([] : hd, tl)         = loop     fs [] []   (hd, tl)
  loop fs [] [] ([], [])              = return fs
  loop fs [] [] ([], tl)              = loop     fs [] []   (reverse tl, [])

  add1 f fs eqs leqs others =
    case addFact f fs of
      Inconsistent   -> mzero
      AlreadyKnown   -> loop fs eqs leqs others
      Improved f1    -> add1 f1 fs eqs leqs others
      Added work fs1 -> withFacts work fs1 eqs leqs others

  isOther p = not (propPred p == Eq || propPred p == Leq)



--------------------------------------------------------------------------------

-- | Inert a new goal to an inetr set.
insertGoal :: Goal -> Inerts -> TCN InsertInert
insertGoal w props =

     do asmps <- assumeGoals wantedList (facts props)
        res <- entails asmps w
        case res of

          NotForAny -> mzero

          YesIf ps proof -> return InsertInert
            { solvedGoals = [ (goalName w, proof) ]
            , newGoals    = ps
            , newFacts    = Props.empty
            , newInerts   = props
            }

          -- More details about this in the note bellow.
          NotForAll ->
                do asmps0       <- assumeGoals [w] (facts props)
                   (solved,new) <- checkExisting [] [] asmps0 wantedList
                   let keepGoal p = not (goalName p `elem` map fst solved)

                   return InsertInert
                     { solvedGoals = solved
                     , newGoals     = new
                     , newFacts     = Props.empty
                     , newInerts =
                        props { goals = Props.insert w
                                        (Props.filter keepGoal (goals props)) }
                     }

  where
  wantedList        = Props.toList (goals props)

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

{- Note: What happens when there is no interaction.

When there is no interaction between the new goal and the existing
we add the new goal to the inert set but, in addition, we check
if it is possible to solve any of the already existing goals in terms
of the new one.  Note that we cannot simply add the existing goals back on the
work queue because this may lead to a non-terminating loop:
any two goals that cannot be solved in terms
of each other are going to keep restarting each other forever.  Instead,
we examine the existing goals one at a time and check for interactions in
the presence of the new goal, removing goals that are entailed, and leaving
goals that result in no interaction in the inert set.
-}






-- Entailment ------------------------------------------------------------------

-- | Answer of entailment.
data Answer = NotForAny           -- ^ The goal is impossible (XXX: add proof?)
            | NotForAll           -- ^ We don't know how to solve this.
            | YesIf [Goal] Proof  -- ^ We solved it in terms of other goals.



entailsSimple :: Facts -> Goal -> TCN Answer
entailsSimple ps p =
  do improved <- impGoal (getEqFacts ps) p
     return
       $ fromMaybe NotForAll
       $ msum [ do (p1,proof) <- improved
                   return (YesIf [p1] proof)

              , do proof <- case goalProp p of
                              Prop Leq [s,t] -> Leq.prove (getLeqFacts ps) s t
                              g -> solve (getOtherFacts ps) g
                   return (YesIf [] proof)
              ]

entails :: Facts -> Goal -> TCN Answer

-- For debugging.
entails ps p | gTrace msg = undefined
  where msg = text "Entails?" $$ nest 2 (vcat (map pp (Facts.toList ps))
                                      $$ text "-----------------"
                                      $$ pp p
                                        )

entails ps p =
  do attempt1 <- entailsSimple ps p
     case attempt1 of
       NotForAll
         | improvable ->    -- Is there room for improvement?

         -- See note bellow for an explanation on what's going on here.
         case assumeGoals [p] ps of

           -- The new goal contradicts the given assumptions.
           Nothing -> return NotForAny

           -- New facts!  We consider only the equalities.
           Just new ->
             do let su1 = getEqFacts new
                eqns <- mapM newGoal $ map factProp $ Subst.toFacts su1
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


{- Note About "Improvement Proper"

This means that we are trying to find a logically equivalent set
of goals that might lead to progress.

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

{-| Given a goal, return a new goal and a proof that
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


--------------------------------------------------------------------------------

solve :: Props Fact -> Prop -> Maybe Proof
solve _ (Prop Eq [x,y])  | x == y           = Just (byRefl x)

solve _ (Prop Leq [x,y]) | x == y           = Just (byLeqRefl x)
solve _ (Prop Leq [Num 0,y])                = Just (byLeq0 y)
solve _ (Prop Leq [Num x, Num y]) | x <= y  = Just (byLeqDef x y)

solve _ (Prop Add [Num 0, y, z]) | y == z   = Just (Using Add0_L [z] [])
solve _ (Prop Add [x, Num 0, z]) | x == z   = Just (Using Add0_R [z] [])
solve _ (Prop Add [Num x, Num y, Num z])
  | x + y == z                              = Just $ Using (DefAdd x y) [] []

solve _ (Prop Mul [Num 0, y, Num 0])        = Just (Using Mul0_L [y] [])
solve _ (Prop Mul [x, Num 0, Num 0])        = Just (Using Mul0_R [x] [])
solve _ (Prop Mul [Num 1, y, z]) | y == z   = Just (Using Mul1_L [z] [])
solve _ (Prop Mul [x, Num 1, z]) | x == z   = Just (Using Mul1_R [z] [])
solve _ (Prop Mul [Num x, Num y, Num z])
  | x * y == z                              = Just $ Using (DefMul x y) [] []

solve _ (Prop Exp [x, Num 0, Num 1])        = Just (Using Exp0_R [x] [])
solve _ (Prop Exp [x, Num 1, z]) | x == z   = Just (Using Exp1_R [z] [])
solve _ (Prop Exp [Num 1, x, Num 1])        = Just (Using Exp1_L [x] [])
solve _ (Prop Exp [Num x, Num y, Num z])
  | x ^ y == z                              = Just $ Using (DefExp x y) [] []

solve ps p =
  do q <- find (\x -> propArgs x == propArgs p) $ getPropsFor (propPred p) ps
     return (factProof q)


impossible :: Prop -> Bool
impossible (Prop Eq  [Num x, Num y])      = not (x == y)

impossible (Prop Leq [Num x, Num y])      = not (x <= y)

impossible (Prop Add [Num x, _, Num y])   = isNothing (minus y x)
impossible (Prop Add [_, Num x, Num y])   = isNothing (minus y x)

impossible (Prop Mul [Num x, _, Num y])
  | x == 0                                = y /= 0
  | x > 0                                 = isNothing (divide y x)

impossible (Prop Mul [_, Num x, Num y])
  | x == 0                                = y /= 0
  | x > 0                                 = isNothing (divide y x)

impossible (Prop Exp [Num x, _, Num y])
  | x == 0                                = y > 1
  | x == 1                                = y /= 1
  | x >  1                                = isNothing (logExact y x)

impossible (Prop Exp [_, Num x, Num y])
  | x == 0                                = y /= 1
  | x  > 0                                = isNothing (rootExact y x)

impossible _                              = False





-- Debugging -------------------------------------------------------------------

ppTrace :: Doc -> a -> a
ppTrace d = trace (show d)

gTrace :: Doc -> Bool
gTrace d = ppTrace d False



