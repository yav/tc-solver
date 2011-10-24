{-# LANGUAGE CPP #-}
module TcTypeNats where

import Control.Monad(foldM,guard,MonadPlus(..))
import Debug.Trace
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List(find)
import Data.Maybe(isJust,isNothing)
import Text.PrettyPrint
import Data.List(zipWith5)

{-------------------------------------------------------------------------------
Terms and Propositions
-------------------------------------------------------------------------------}

type Var  = Xi

{- The 'Xi' in the 'Num' constructor stores the original 'Xi' type that
gave rise to the number. It is there in an attempt to preserve type synonyms. -}
data Term = Var Var
          | Num Integer (Maybe Xi)
            deriving (Eq,Ord)

num :: Integer -> Term
num n = Num n Nothing


data Pred = Add | Mul | Exp | Leq | Eq
            deriving (Show, Eq, Ord)

arity :: Pred -> Int
arity pr =
  case pr of
    Add -> 3
    Mul -> 3
    Exp -> 3
    Leq -> 2
    Eq  -> 2

data Prop = Prop Pred [Term]
            deriving (Eq,Ord)

wfProp :: Prop -> Bool
wfProp (Prop p xs) = arity p == length xs


{-------------------------------------------------------------------------------
Convenient access to propositions embedded inside other types
-------------------------------------------------------------------------------}

class HasProp a where
  getProp :: a -> Prop

instance HasProp Prop where getProp = id

propPred :: HasProp a => a -> Pred
propPred p = case getProp p of
               Prop x _ -> x

propArgs :: HasProp a => a -> [Term]
propArgs p = case getProp p of
               Prop _ xs -> xs




{-------------------------------------------------------------------------------
Collections of Entities with Propositions

Throughout the development we work with collections of propositions.
One way to represent such collections is, simply, to use linked lists.
However, because we often need to search for propositions
of a certain form, it is more convenient (and efficient) to group
propositions with the same predicate constructor together.
-------------------------------------------------------------------------------}

-- | We use a finite map that maps predicate constructors to the
-- entities containing propositions with the corresponding constructor.
newtype Props a = P (M.Map Pred (S.Set a))

-- | Convert a set of propositions back into its list representation.
propsToList :: Ord a => Props a -> [a]
propsToList (P ps) = S.toList $ S.unions $ M.elems ps

-- | An empty set of propositions.
noProps :: Props a
noProps = P M.empty

-- | Add a proposition to an existing set.
insertProps :: (Ord a, HasProp a) => a -> Props a -> Props a
insertProps p (P ps) = P (M.insertWith S.union (propPred p) (S.singleton p) ps)

-- | Convert a list of propositions into a set.
propsFromList :: (Ord a, HasProp a) => [a] -> Props a
propsFromList = foldr insertProps noProps

-- | Combine the propositions from two sets.
unionProps :: Ord a => Props a -> Props a -> Props a
unionProps (P as) (P bs) = P (M.unionWith S.union as bs)

-- | Pick one of the propositions from a set
-- and return the remaining propositions.
-- Returns 'Nothing' if the set is empty.
getOne :: Props a -> Maybe (a, Props a)
getOne (P ps) =
  do ((op,terms),qs) <- M.minViewWithKey ps
     (t,ts)          <- S.minView terms
     return (t, if S.null ts then P qs else P (M.insert op ts qs))

-- | Pick one of the propositions from a set in all possible ways.
chooseProp :: (Ord a, HasProp a) => Props a -> [(a,Props a)]
chooseProp ps =
  case getOne ps of
    Nothing -> []
    Just (q,qs) -> (q,qs) : [ (a,insertProps q as) | (a,as) <- chooseProp qs ]

-- | Get the arguments of propositions constructed with a given
-- predicate constructor.
getPropsFor :: Pred -> Props a -> [a]
getPropsFor op (P ps) = S.toList (M.findWithDefault S.empty op ps)

getPropsForRaw :: Pred -> Props Fact -> [([Term],Proof)]
getPropsForRaw p ps = [ (propArgs q, factProof q) | q <- getPropsFor p ps ]


-- | Returns 'True' if the set is empty.
isEmptyProps :: Props a -> Bool
isEmptyProps (P ps) = M.null ps

mapProps :: (Ord a, Ord b) => (a -> b) -> Props a -> Props b
mapProps f (P m) = P (fmap (S.map f) m)

-- | Remove propositions that do not satisfy the given predicate.
filterProps :: (Ord a, HasProp a) => (a -> Bool) -> Props a -> Props a
filterProps p (P ps) = P (M.mapMaybeWithKey upd ps)
  where upd _ ts = let xs = S.filter p ts
                   in if S.null xs then Nothing else Just xs

-- | Remove propositions with the given predicate constructor.
rmPropsFor :: Pred -> Props a -> Props a
rmPropsFor op (P as) = P (M.delete op as)


{-------------------------------------------------------------------------------
Assumptions and Goals

The solver manipulates two kinds of propositions: {\em given} propositions
correspond to assumptions that have known proofs,
while {\em wanted} propositions correspond to goals that need to be proved.
-------------------------------------------------------------------------------}

data Goal = Goal { goalName  :: EvVar, goalProp :: Prop }
            deriving (Eq,Ord)

data Fact = Fact { factProof :: Proof, factProp :: Prop }

instance HasProp Goal where getProp = goalProp
instance HasProp Fact where getProp = factProp


{- We compare facts only based on the property they state because we are
not interested in facts that state the same thing but differ in the proof. -}

instance Eq Fact where
  x == y = factProp x == factProp y

instance Ord Fact where
  compare x y = compare (factProp x) (factProp y)



{- The function 'goalToFact' is used when we attempt to solve a new goal
in terms of already existing goals. -}
goalToFact :: Goal -> Fact
goalToFact g = Fact { factProof = ByAsmp (goalName g), factProp = goalProp g }


{- A part of the solver's state keeps track of the current set of known facts,
and the goals that still need to be solved. -}

data SolverProps = SolverProps { given :: Props Fact, wanted :: Props Goal }

noSolverProps :: SolverProps
noSolverProps = SolverProps { given = noProps, wanted = noProps }

insertGiven :: Fact -> SolverProps -> SolverProps
insertGiven g ps = ps { given = insertProps g (given ps) }

insertWanted :: Goal -> SolverProps -> SolverProps
insertWanted w ps = ps { wanted = insertProps w (wanted ps) }

unionSolverProps :: SolverProps -> SolverProps -> SolverProps
unionSolverProps ps1 ps2 = SolverProps
                             { given  = unionProps (given ps1) (given ps2)
                             , wanted = unionProps (wanted ps1) (wanted ps2)
                             }




{-------------------------------------------------------------------------------
Proofs and Theorems
-------------------------------------------------------------------------------}

data Theorem  = AssumedFalse
              | EqRefl      -- forall a. a = a
              | EqSym       -- forall a b. (a = b) => b = a
              | EqTrans     -- forall a b c. (a = b, b = c) => a = c
              | Cong Pred   -- forall xs ys. (xs = ys, F xs) => F ys
              | AddLeq
              | MulLeq
              | ExpLeq1
              | ExpLeq2
              | DefAdd Integer Integer Integer
              | DefMul Integer Integer Integer
              | DefExp Integer Integer Integer
              | DefLeq Integer Integer
              | LeqRefl
              | LeqAsym
              | LeqTrans
              | Leq0 | Add0 | Mul0 | Mul1 | Root0 | Root1 | Log1
              | AddComm | MulComm
              | SubL | SubR | DivL | DivR | Root | Log
              | AddAssoc | MulAssoc | AddMul | MulExp | ExpAdd | ExpMul
              | AddAssocSym | MulAssocSym | AddMulSym
              | MulExpSym | ExpAddSym | ExpMulSym
              | FunAdd | FunMul | FunExp
                deriving Show

data Proof    = ByAsmp EvVar
              | Using Theorem [Term] [Proof]   -- Instantiation, sub-proofs

byRefl :: Term -> Proof
byRefl t = Using EqRefl [t] []

bySym :: Term -> Term -> Proof -> Proof
bySym _ _ p@(Using EqRefl _ _) = p
bySym _ _ (Using EqSym _ [p]) = p
bySym t1 t2 p = Using EqSym [t1,t2] [p]

byTrans :: Term -> Term -> Term -> Proof -> Proof -> Proof
-- byTrans t1 t2 _ p1 p2 = byCong Eq [ bySym t1 t2 p1, p2 ] (byRefl t2)
-- (r = s, s = t) => r = t
-- cong = (s = r, s = t, s = s
byTrans _ _ _ (Using EqRefl _ _) p = p
byTrans _ _ _ p (Using EqRefl _ _) = p
byTrans t1 t2 t3 p1 p2 = Using EqTrans [t1,t2,t3] [p1,p2]

-- (x1 = y1, x2 = y2, P x1 x2) => P y1 y2
byCong :: Pred -> [Term] -> [Proof] -> Proof -> Proof
byCong _ _ qs q | all isRefl qs = q
  where isRefl (Using EqRefl _ _) = True
        isRefl _ = False
-- (x1 == y1, x2 == y2, x1 == x2) => y1 = y2
byCong Eq [x1,x2,y1,y2] [ xy1, xy2 ] xx =
                  byTrans y1 x2 y2 (byTrans y1 x1 x2 (bySym x1 y1 xy1) xx) xy2
-- (p1: x1 = y1, p2: x2 = y2,
--     byCong (q1 : a1 = x1) (q2 : a2 = x2) (q : F z1 z2) : F y1 y2)
-- => byCong F (as ++ ys) (trans q1 p1, trans q2 p2) q
byCong p ts ps (Using (Cong _) us qs0) =
  let qs = init qs0
      q  = last qs0

      as      = take (arity p) us
      (xs,ys) = splitAt (arity p) ts

  in byCong p (as ++ ys) (zipWith5 byTrans as xs ys qs ps) q

byCong p ts qs q = Using (Cong p) ts (qs ++ [q])


proofLet :: EvVar -> Proof -> Proof -> Proof
proofLet x p1 (ByAsmp y) | x == y     = p1
                         | otherwise  = ByAsmp y
proofLet x p1 (Using EqTrans [t1,t2,t3] [s1,s2]) =
  byTrans t1 t2 t3 (proofLet x p1 s1) (proofLet x p1 s2)
proofLet x p1 (Using EqSym [t1,t2] [s1]) =
  bySym t1 t2 (proofLet x p1 s1)
proofLet x p1 (Using (Cong p) ts ss) = byCong p ts (init ss1) (last ss1)
  where ss1 = map (proofLet x p1) ss
proofLet x p1 (Using t ts ps) = Using t ts (map (proofLet x p1) ps)

byFalse :: Proof
byFalse = Using AssumedFalse [] []

{-------------------------------------------------------------------------------
Results of Entailement
-------------------------------------------------------------------------------}

{- | The entailment function may return one of three possible answers,
informally corresponding to ``certainly not'', ''not in its current form'',
and ''(a qualified) yes''. -}
data Answer = NotForAny | NotForAll | YesIf (Props Goal) Proof

isNotForAny :: Answer -> Bool
isNotForAny NotForAny = True
isNotForAny _         = False

isNotForAll :: Answer -> Bool
isNotForAll NotForAll = True
isNotForAll _         = False

isYesIf :: Answer -> Bool
isYesIf (YesIf _ _)   = True
isYesIf _             = False




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
The Inert Props

The {\em inert set} is a collection of propositions, which keeps track
of the facts that are known by the solver, as well as any goals that
were attempted but not solved.  We refer to this set as ``inert'' because
the propositions in it cannot ``interact'' with each other.
-------------------------------------------------------------------------------}

-- | To distinguish sets with this property from other sets of propositions
-- we use a separate type synonym.
type InertProps = SolverProps

-- | More formally, the following predicate captures the ``non-interacion''
-- invariant of the inert set:
inert_prop :: InertProps -> TCN ()
inert_prop props =
  do -- sequence_ [ noInteraction gs g | (g, gs) <- chooseProp givens  ]
     sequence_ [ noInteraction (assuming ws) w | (w, ws) <- chooseProp wanteds ]

  where givens      = given props
        wanteds     = wanted props
        assuming ws = unionProps (mapProps goalToFact ws) givens
        noInteraction as b = (guard . isNotForAll) =<< entails as b

{- The predicate consists of two parts, both of the same form:  the first one
asserts that the collection of given facts is consistent and non-redundant,
while the second asserts the same property for the set of goals.
The ``consistent and non-redundant'' property is captured
by the requirement that when we use the entailment function we get
the answer \Verb"NotForAll"---had we obtained \Verb"NotForAny", we would
have a constradiction and hence the propositions would not be consistent,
and if we obtained \Verb"YesIf", then then the proposition would
be redundant and hence may be eliminated.  The predicate makes use
of the auxiliary function \Verb"chooseProp", which extracts a single
element from a collection in all possible ways.  -}


addGiven  :: Fact -> InertProps -> TCN PassResult
addWanted :: Goal -> InertProps -> TCN PassResult

data PassResult = PassResult { dropWanted   :: [EvVar]
                             , solvedWanted :: [(EvVar,Proof)]
                             , newWork      :: SolverProps
                             , consumed     :: Bool
                             }



{-------------------------------------------------------------------------------
Adding a New Assumption (given)

When we add a new assumption to an inert set we check for ``interactions''
with the existing assumptions by using the entailment function.
-------------------------------------------------------------------------------}

-- NOTE: Since we recompute the closure of the givens all the
-- time, we could simply add all the known facts, and not worry about
-- interactions...

-- XXX: We should probably just cache the closure
addGiven g props =
  case solve (given props) (factProp g) of
    Just _ -> return PassResult
                { dropWanted = []
                , solvedWanted = []
                , newWork = noSolverProps
                , consumed = True
                }
    _ -> case closure (insertProps g (given props)) of
           Nothing -> mzero
           Just _ -> return PassResult
             { dropWanted    = map goalName (propsToList (wanted props))
             , solvedWanted  = []
             , newWork       = props { given = noProps }
             , consumed      = False
             }


{-

  case entails (given props) (factProp g) of

{- The first possibility is that the new assumption is incompatible with
the existing assumptions, in which case we simply report an error
and ignore the new fact. -}

    NotForAny -> mzero

{- Another possible outcome is that---in its current form---the proposition
is already entailed by the currently known assumptions.  Then, we leave
the inert set unmodified but we record the alternative formulation (if any)
as new work to be processed by the solver. -}

    YesIf ps _ -> return PassResult
      { dropWanted    = []
      , solvedWanted  = []
      , newWork       = undefined -- emptySolverProps { given = ps } -- XXX: type error
      , newGoals      = noProps
      , consumed      = True
      }

{- Finally, if entailment yielded no interaction, then we add the new fact to
the inert set.  Any goals that were in the inert set are removed and added
back to the work queue so that we can re-process them in the context of the
new assumption. -}

    NotForAll -> return PassResult
      { dropWanted    = map goalName (propsToList (wanted props))
      , solvedWanted  = []
      , newWork       = props { given = noProps }
      , newGoals      = noProps
      , consumed      = False
      }
-}


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

addWanted w props =

  do res <- entails (assuming (wanted props)) w
     case res of

{- The first two cases---when there is interaction---are the same as for
adding an assumption:  inconsistencies result in an error, while solving
the new goal does not affect the inert set but may add a new formulation
of the goal to the work queue. -}

      NotForAny -> mzero

      YesIf ps proof -> return PassResult
        { dropWanted    = []
        , solvedWanted  = [ (goalName w, proof) ]
        , newWork       = noSolverProps { wanted = ps }
        , consumed      = True
        }

{- The major difference in the algorithm is when there is no interaction
between the new goal and the existing inert set.  In this case we
add the new goal to the inert set but, in addition, we need to check
if it is possible to solve any of the already existing goals in terms
of the new goal.  We cannot simply add the existing goals back on the
work queue (as we did when we added an assumption) because this may
lead to a non-terminating loop:  any two goals that cannot be solved in terms
of each other are going to keep restarting each other forever.  Instead,
we examine the existing goals one at a time and check for interactions in
the presence of the new goal, removing goals that are entailed, and leaving
goals that result in no interaction in the inert set. -}

      NotForAll ->
        do let start = ([],noProps)
           (solved,new) <- foldM check start (chooseProp (wanted props))

           return PassResult
             { dropWanted   = map fst solved
             , solvedWanted = solved
             , newWork      = noSolverProps { wanted = new }
             , consumed     = False
             }

{- The function \Verb"check" has the details of how to check for interaction
between some existing goal, \Verb"w1", and the new goal \Verb"w".  The
set \Verb"ws" has all existing goals without the goal under consideration. -}

  where
  assuming ws = unionProps (mapProps goalToFact ws) (given props)

  check (solved, new) (w1,ws) =
    do res <- entails (assuming (insertProps w ws)) w1
       case res of
         NotForAny      -> mzero
         NotForAll      -> return (solved, new)
         YesIf ps proof -> return ( (goalName w1, proof) : solved
                                  , unionProps ps new
                                  )


{- To see the algorithm in action, consider the following example:

New goal:   2 <= x
Inert set:  { wanted = [1 <= x, x + 5 = y] }

Step 1: entails [1 <= x, x + 5 = y] (2 <= x)      -->  NotForAll
Step 2: Add (2 <= x) to the inert set and examine existing goals:
  Step 2.1: entails [2 <= x, x + 5 = y] (1 <= x)  --> YesIf []  // remove
  Step 2.2: entails [2 <= x, 1 <= x] (x + 5 = y)  --> NotForAll // keep

New inert set: { wanted = [2 <= x, x + 5 = y] }

-}


{-------------------------------------------------------------------------------
Entailment

A central component of the solver is the entailment function, which determines
if a set of assumptions (the first argument), entail a certain proposition
(the second argument).
-------------------------------------------------------------------------------}





entails :: Props Fact -> Goal -> TCN Answer
entails ps p | gTrace msg = undefined
  where msg = text "Entails?" $$ nest 2 (vcat (map pp (propsToList ps))
                                      $$ text "-----------------"
                                      $$ pp p
                                        )


entails ps' p' =
  case closure ps' of
    Nothing -> return (YesIf noProps byFalse) -- Assumed False. XXX: Could record proof
    Just (su,ps) ->
      do (p,p_su) <- impGoal su p'
         case solve ps (goalProp p) of

           Just proof ->
             return (YesIf noProps $ proofLet (goalName p) proof p_su)

           Nothing ->

            -- This is what we'll do if the additional improvements fail.
            let noLuck = return $ if goalName p == goalName p'
                                    then NotForAll
                                    else YesIf (insertProps p noProps) p_su

            in -- Try improvement
            case closure (insertProps (goalToFact p) ps) of
              Nothing -> return NotForAny
              Just (su1,_) ->
                case goalProp p' of
                  Prop Eq [Var x, t]
                    -- Do the "better" goals contain original?
                    | any (\(x',t',_) -> x == x' && t == t') su1 -> noLuck

                  _ -> -- No?  So, then there's still hope.

                       -- First, we replace the fake facts by goals.
                    do let fixup (x,t,_) =
                              do g <- newGoal (Prop Eq [Var x, t])
                                 return (g, (x,t,ByAsmp (goalName g)))

                       (eqns,su2) <- unzip `fmap` mapM fixup su1

                       let -- Make some new facts, using existing facts
                           -- and the new equality assumptions.
                           ps1 = impAsmps su2 ps

                           -- Make a new (better) goal,
                           -- using the equality assumptions
                           -- p_su2:  p <=> p1
                       (p1,p_su2) <- impGoal su2 p

                       case solve ps1 (goalProp p1) of
                         Nothing -> noLuck  -- Aw, nothing works!

                         -- It worked!
                         Just proof ->
                             return $ YesIf (propsFromList eqns)
                                    $ proofLet (goalName p1) proof
                                    $ proofLet (goalName p)  p_su2 p_su

closure :: Props Fact -> Maybe (Subst, Props Fact)
closure ps = closure1 =<< improvingSubst ps

closure1 :: (Subst, Props Fact) -> Maybe (Subst, Props Fact)
closure1 (su0, ps0) =
  do (su, ps) <- improvingSubst
               $ propsFromList
               $ do (q,qs) <- chooseProp ps0
                    i      <- implied qs q
                    guard (isNothing (solve ps0 (factProp i)))
                    return i

     let su1 = compose su su0
         ps1 = filterProps (not . trivial . factProp) (impAsmps su ps0)

     if isEmptyProps ps
       then tr "computed closure:" (propsToList ps1)
           $ return (su1, ps1)
       else tr "adding:" (propsToList ps) $ closure1 (su1, unionProps ps ps1)


{-------------------------------------------------------------------------------
Proprties of the Entailment Function
-------------------------------------------------------------------------------}

-- | Adding more assumptions cannot make things less contradictory
entails_any_prop :: Props Fact -> Goal -> Fact -> TCN ()
entails_any_prop ps q p =
  do res <- entails ps q
     case res of
       NotForAny -> (guard . isNotForAny) =<< entails (insertProps p ps) q
       _         -> return ()


-- | Dropping assumptions cannot make things more contradictory or more defined.
enatils_all_prop :: Fact -> Props Fact -> Goal -> TCN ()
enatils_all_prop p ps q =
  do ans <- entails (insertProps p ps) q
     case ans of
       NotForAll -> (guard . isNotForAll) =<< entails ps q
       _         -> return ()


{-------------------------------------------------------------------------------
-- Substitutions
-------------------------------------------------------------------------------}

-- The 3rd elemnt of the tuple is a proof that the variable equals the term.
type Subst  = [ (Var,Term, Proof) ]


compose :: Subst -> Subst -> Subst
compose s2 s1 =
  [ (x, t2, byTrans (Var x) t t2 p1 p2)
                    | (x,t,p1) <- s1, let (t2,p2) = apSubst s2 t ] ++
  [ z | z@(x,_,_) <- s2, all (not . eqType x . fst3) s1 ]
  where fst3 (x,_,_) = x

-- For simple terms no need to occur check
mgu :: Proof -> Term -> Term -> Maybe Subst
mgu _ x y | x == y   = return []
mgu ev (Var x) t     = return [(x,t,ev)]
mgu ev t (Var x)     = return [(x,t,ev)]
mgu _ _ _              = mzero

-- The proof here is that the two terms are euqal, as long 
-- as the equations are equalities.  For example,
-- if the substitutions is { ev: x = 3 }, and we have the term "x"
-- then we would get the term "3" and 'ev', a proof that "x = 3"
apSubst :: Subst -> Term -> (Term, Proof)
apSubst su (Var x)
  | (t1,ev) : _ <- [ (t1,ev) | (y,t1,ev) <- su, eqType x y ] = (t1,ev)
apSubst _ t           = (t, byRefl t)

-- Given a goal, return a potentially new goal, and a proof which
-- would solve the old goal in terms of the new one.
impGoal :: Subst -> Goal -> TCN (Goal, Proof)
impGoal su p
  | null su || propArgs p == ts  = return (p, ByAsmp (goalName p))
  | otherwise = do g <- newGoal (Prop (propPred p) ts)
                   return (g, byCong (propPred p)
                                (ts ++ propArgs p)
                                (zipWith3 bySym (propArgs p) ts evs)
                                (ByAsmp (goalName g)))
  where (ts,evs) = unzip $ map (apSubst su) (propArgs p)

-- If "A : P x", and "B : x = 3", then "ByCong P [B] A : P 3"
impAsmp :: Subst -> Fact -> Fact
impAsmp su p = p { factProof = byCong (propPred p) (propArgs p ++ ts)
                                                          evs (factProof p)
                 , factProp  = Prop (propPred p) ts
                 }
  where (ts,evs) = unzip $ map (apSubst su) (propArgs p)


impAsmps :: Subst -> Props Fact -> Props Fact
impAsmps su = mapProps (impAsmp su)




-- | Represent a substitution as a set of equations.
substToEqns :: Subst -> Props Fact
substToEqns su = propsFromList (map mk su)
  where mk (x,t,ev) = Fact { factProof = ev
                           , factProp  = Prop Eq [Var x, t]
                           }


-- x = 2, x + y = 3

-- x = 2 => 2 + y = 3

-- | Turn the equations that we have into a substitution, and return
-- the remaining propositions with the substitution applied to them.
-- XXX: It might be better to simply keep these equations as
-- substitutions in the 'Props' type.
improvingSubst :: Props Fact -> Maybe (Subst, Props Fact)
improvingSubst ps  = do su <- loop [] (getPropsFor Eq ps)
                        return (su, filterProps (not . trivial . factProp)
                                   $ impAsmps su $ rmPropsFor Eq ps)
  where
  loop su (eq : eqs) =
    do let [x,y] = propArgs eq
       su1 <- mgu (factProof eq) x y
       loop (compose su1 su) (map (impAsmp su1) eqs)
  loop su [] = return su



trivial :: Prop -> Bool
trivial = isJust . solve noProps

solve :: Props Fact -> Prop -> Maybe Proof
solve  _ (Prop Eq [x,y]) | x == y = Just (byRefl x)
solve ps p = solve0 [] p `mplus` byAsmp ps p

byAsmp :: Props Fact -> Prop -> Maybe Proof
byAsmp ps p =
  do q <- find (\x -> propArgs x == propArgs p) $ getPropsFor (propPred p) ps
     return (factProof q)



{-------------------------------------------------------------------------------
Testing without GHC
-------------------------------------------------------------------------------}

#define TEST_WITHOUT_GHC 1
#ifdef TEST_WITHOUT_GHC

type Xi    = String
type EvVar = String

newtype TCN a = T { runTCN :: String -> Int -> Maybe (a,Int) }

instance Functor TCN where
  fmap f m = do x <- m
                return (f x)

instance Monad TCN where
  return x  = T $ \_ s -> return (x,s)
  T m >>= f = T $ \r s -> do (a,s1) <- m r s
                             let T m1   = f a
                             m1 r $! s1

instance MonadPlus TCN where
  mzero = T (\_ _ -> Nothing)
  mplus = error "mplus is unused"


eqType :: Xi -> Xi -> Bool
eqType = (==)

newGoal :: Prop -> TCN Goal
newGoal p = T $ \r s ->
  do let s1 = s + 1
     s1 `seq` Just (Goal { goalName = r ++ "_" ++ show s, goalProp = p }, s1)


{-------------------------------------------------------------------------------
The Solver

The purpose of the solver is to turn an arbitrary set of propositions
into an inert one.  This is done by starting with some inert set
(e.g., the empty set of propositions) and then adding each new proposition
one at a time.  Assumptions and goals are added in different ways, so
we have two different functions to add a proposition to an existing
inert set.

If successful, both functions return a \Verb"PassResult" value, which
contains an updated inert set and, potentially, some additional propositions
that need to be added to the set.  The actual solver just keeps using these
two functions until it runs out of work to do.
Note that we start by first adding all assumptions, and only then we consider
the goals because the assumptions might help us to solve the goals.
-------------------------------------------------------------------------------}

type SolverS = (InertProps, [(EvVar,Proof)])

addWorkItems :: SolverProps -> SolverS -> String -> Int -> Maybe SolverS
addWorkItems ps is r s = fst `fmap` runTCN (addWorkItemsM ps is) r s

addWorkItemsM :: SolverProps -> SolverS -> TCN SolverS
addWorkItemsM ps ss@(is,solns) =
 case getOne (given ps) of
   Just (g,gs) ->
     do r <- addGiven g is
        let js = mkInert (insertGiven g) r
        addWorkItemsM (unionSolverProps (newWork r) ps { given = gs }) (js,solns)

   Nothing ->
     case getOne (wanted ps) of
       Just (w,ws) ->
         do r <- addWanted w is
            let js = mkInert (insertWanted w) r
            addWorkItemsM (unionSolverProps (newWork r) ps { wanted = ws })
                                          (js, solvedWanted r ++ solns)
       Nothing -> return ss

  where
  mkInert add r =
    let as = case dropWanted r of
               [] -> is
               ns -> is { wanted = filterProps (keep ns) (wanted is) }
    in if consumed r then as else add as
  keep ns p = not (goalName p `elem` ns)


--------------------------------------------------------------------------------
#else
--------------------------------------------------------------------------------

{- Inetrface with GHC's solver -}

-- We keep the original type in numeric constants to preserve type synonyms.
toTerm :: Xi -> Term
toTerm xi = case mplus (isNumberTy xi) (isNumberTy =<< tcView xi) of
              Just n -> Num n (Just xi)
              _      -> Var xi

toProp :: CanonicalCt -> Prop
toProp (CDictCan { cc_class = c, cc_tyargs = xis })
  | className c == lessThanEqualClassName = Prop Leq (map toTerm xis)

toProp (CFunEqCan { cc_fun = tc, cc_tyargs = xis, cc_rhs = xi2 })
  | tyConName tc == addTyFamName = Prop Add (ts ++ [t])
  | tyConName tc == mulTyFamName = Prop Mul (ts ++ [t])
  | tyConName tc == expTyFamName = Prop Exp (ts ++ [t])

    where ts = map toTerm xis
          t  = toTerm xi2

toProp p = panic $
  "[TcTypeNats.toProp] Unexpected CanonicalCt: " ++ showSDoc (ppr p)


toInert :: CanonicalCts -> CanonicalCts -> InertProps
toInert gs ws = SolverProps { given  = listToProps (bagToList gs)
                        , wanted = listToProps (bagToList ws)
                        }



fromTerm :: Term -> Xi
fromTerm (Num n mb) = fromMaybe (mkNumberTy n) mb
fromTerm (Var xi)   = xi


data CvtProp  = CvtClass Class [Type]
              | CvtCo Type Type

fromProp :: Prop -> TcS CvtProp
fromProp (Prop p ts) =
  case p of
    Leq -> do cl <- tcsLookupClass lessThanEqualClassName
              return (CvtClass cl (map fromTerm ts))
    Eq -> case ts of
            [t1,t2] -> return $ CvtCo (fromTerm t1) (fromTerm t2)
            _ -> panic $ "[TcTypeNats.fromProp] Malformed Eq prop"

    Add -> mkFun `fmap` tcsLookupTyCon addTyFamName
    Mul -> mkFun `fmap` tcsLookupTyCon mulTyFamName
    Exp -> mkFun `fmap` tcsLookupTyCon expTyFamName

  where mkFun tc = do let ts1 = map fromTerm ts
                      return $ CvtCo (mkTyConApp tc (init ts1)) (last ts1)

newSubGoal :: CvtProp -> TcS EvVar
newSubGoal (CvtClass c ts) = newDictVar c ts
newSubGoal (CvtCo t1 t2)   = newCoVar t1 t2

newFact :: CvtProp -> TcS EvVar
newFact prop =
  do d <- newSubGoal prop
     defineDummy d prop
     return d


-- If we decided that we want to generate evidence terms,
-- here we would set the evidence properly.  For now, we skip this
-- step because evidence terms are not used for anything, and they
-- get quite large, at least, if we start with a small set of axioms.
defineDummy :: EvVar -> CvtProp -> TcS ()
defineDummy d (CvtClass c ts) =
  setDictBind d $ EvAxiom "<=" $ mkTyConApp (classTyCon c) ts

defineDummy c (CvtCo t1 t2) =
  setCoBind c (mkUnsafeCo t1 t2)


data NumericsResult = NumericsResult
  { numNewWork :: WorkList
  , numInert   :: Maybe CanonicalCts   -- Nothing for "no change"
  , numNext    :: Maybe CanonicalCt
  }


toNumericsResult :: CanonicalCt -> Maybe PassResult -> TcS NumericsResult
toNumericsResult prop Nothing = impossible prop
toNumericsResult prop (Just res) =
  return NumericsResult
    { numNext = if consumed res then Nothing else prop
    }


impossible :: CanonicalCt -> TcS NumericsResult
impossible c =
  do numTrace "Impossible" empty
     let err = mkFrozenError (cc_flavor c) (cc_id c)
     return NumericsResult
       { numNext = Just err, numInert = Nothing, numNewWork = emptyWorkList }




-- XXX: What do we do with "derived"?
canonicalNum :: CanonicalCts -> CanonicalCts -> CanonicalCts -> CanonicalCt ->
                TcS NumericsResult
canonicalNum given derived wanted prop0 =
  let inert = toInert given wanted
      new   = toProp prop0
  in case cc_flavor prop of
       Wanted {}   -> toNumericsResult prop0 $ addWanted inert new
       Derived {}  -> doNothing
       Given {}    -> toNumericsResult prop0 $ addGiven inert new

  where
  -- Disables the solver.
  doNothing = return NumericsResult { numInert    = Nothing
                                    , numNewWork  = emptyWorkList
                                    , numNext     = Just prop0
                                    }


#endif

{-------------------------------------------------------------------------------
Functions on natural numbers.
-------------------------------------------------------------------------------}

minus :: Integer -> Integer -> Maybe Integer
minus x y = if x >= y then Just (x - y) else Nothing

descreteRoot :: Integer -> Integer -> Maybe Integer
descreteRoot root x0 = search 0 x0
  where
  search from to = let x = from + div (to - from) 2
                       a = x ^ root
                   in case compare a x0 of
                        EQ              -> Just x
                        LT | x /= from  -> search x to
                        GT | x /= to    -> search from x
                        _               -> Nothing

descreteLog :: Integer -> Integer -> Maybe Integer
descreteLog _    0   = Just 0
descreteLog base x0 | base == x0  = Just 1
descreteLog base x0 = case divMod x0 base of
                         (x,0) -> fmap (1+) (descreteLog base x)
                         _     -> Nothing

divide :: Integer -> Integer -> Maybe Integer
divide _ 0  = Nothing
divide x y  = case divMod x y of
                (a,0) -> Just a
                _     -> Nothing

{-------------------------------------------------------------------------------
Pretty Printing
-------------------------------------------------------------------------------}

class PP a where
  pp :: a -> Doc

instance PP Term where
  pp (Var x)    = text x
  pp (Num x _)  = integer x

instance PP Pred where
  pp op =
    case op of
      Add -> text "+"
      Mul -> text "*"
      Exp -> text "^"
      Leq -> text "<="
      Eq  -> text "=="

instance PP Prop where

  pp (Prop op [t1,t2,t3])
    | op == Add || op == Mul || op == Exp =
      pp t1 <+> pp op <+> pp t2 <+> text "==" <+> pp t3

  pp (Prop op [t1,t2])
    | op == Leq || op == Eq = pp t1 <+> pp op <+> pp t2

  pp (Prop op ts) = pp op <+> fsep (map pp ts)


instance PP Fact where
  pp f = text "G:" <+> pp (factProp f)

instance PP Goal where
  pp f = text "W:" <+> pp (goalProp f)


instance PP Proof where
  pp (ByAsmp e) = text e
  pp (Using x ts ps) = text (show x) <> inst $$ nest 2 (vcat (map pp ps))
    where inst = case ts of
                   [] -> empty
                   _  -> text "@" <> parens (fsep $ punctuate comma $ map pp ts)

instance (Ord a, PP a) => PP (Props a) where
  pp = vcat . map pp . propsToList


instance PP SolverProps where
  pp is = vcat ( map pp (propsToList (given is))
              ++ map pp (propsToList (wanted is))
               )




{-------------------------------------------------------------------------------
Misc.
-------------------------------------------------------------------------------}

-- | Choce an element from a list in all possible ways.
choose :: [a] -> [(a,[a])]
choose []     = []
choose (x:xs) = (x,xs) : [ (y, x:ys) | (y,ys) <- choose xs ]

-- | For debuging lists of things.
tr :: PP a => String -> [a] -> b -> b
tr x ys z = trace x (trace msg z)
  where msg = case ys of
                [] -> "  (empty)"
                _  -> show $ nest 2 $ vcat $ map pp ys

ppTrace :: Doc -> a -> a
ppTrace d = trace (show d)

gTrace :: Doc -> Bool
gTrace d = ppTrace d False

#include "TcTypeNatsRules.hs"


