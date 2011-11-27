{-# LANGUAGE CPP #-}
module TcTypeNats where

import Control.Monad(foldM,guard,MonadPlus(..),msum)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List(find)
import Data.Maybe(fromMaybe,isNothing)
import Data.Either(partitionEithers)
import Text.PrettyPrint
import Data.List(zipWith5)
import Debug.Trace

{-------------------------------------------------------------------------------
Terms and Propositions
-------------------------------------------------------------------------------}

newtype Var = V Xi
              deriving Show

{- The 'Xi' in the 'Num' constructor stores the original 'Xi' type that
gave rise to the number. It is there in an attempt to preserve type synonyms. -}

{- The ordering model below makes assumption about this ordering:
  - Variables should come before numbers.  This is useful because we can
    use "fst (split 0)" to get just the variable part of the map.
  - Number-terms should be ordered as their corresponding numbers.  This is
    useful so that we can use "splitLookup n" to find information about
    a number and its neighbours.
-}

data Term = Var Var
          | Num Integer (Maybe Xi)
            deriving (Eq,Ord,Show)

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

-- | Get the arguments of propositions constructed with a given
-- predicate constructor.
getPropsFor :: Pred -> Props a -> [a]
getPropsFor op (P ps) = S.toList (M.findWithDefault S.empty op ps)

-- | Like 'getPropsFor' but selecting 2 distinct propositions at a time.
-- We return all permutations of the proporsitions.
getPropsFor2 :: Pred -> Props a -> [(a,a)]
getPropsFor2 op ps =
  do (a,as) <- choose $ getPropsFor op ps
     b      <- as
     return (a,b)

-- | Like 'getPropsFor' but selecting 3 distinct propositions at a time.
-- We return all permutations of the proporsitions.
getPropsFor3 :: Pred -> Props a -> [(a,a,a)]
getPropsFor3 op ps =
  do (a,as) <- choose $ getPropsFor op ps
     (b,bs) <- choose as
     c      <- bs
     return (a,b,c)


-- | Returns 'True' if the set is empty.
isEmptyProps :: Props a -> Bool
isEmptyProps (P ps) = M.null ps

-- | Remove propositions that do not satisfy the given predicate.
filterProps :: (Ord a, HasProp a) => (a -> Bool) -> Props a -> Props a
filterProps p (P ps) = P (M.mapMaybeWithKey upd ps)
  where upd _ ts = let xs = S.filter p ts
                   in if S.null xs then Nothing else Just xs

{- Apply a function to all memerbs, and keep only the ones that do
not change (i.e., the parameter returns 'Nothing').  The new values
of the members that did change are returned in a list. -}

mapExtract :: (Ord a, HasProp a) =>
              (a -> Maybe a) -> Props a -> ([a], Props a)
mapExtract f ps = case partitionEithers $ map apply $ propsToList ps of
                    (remains,changed) -> (changed, propsFromList remains)
  where apply x = case f x of
                    Nothing -> Left x
                    Just a  -> Right a


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


{- We compare facts based only on the property they state because we are
not interested in facts that state the same thing but differ in the proof. -}

instance Eq Fact where
  x == y = factProp x == factProp y

instance Ord Fact where
  compare x y = compare (factProp x) (factProp y)


--------------------------------------------------------------------------------

{- A collection of unprocessed facts.  When processing facts, it is more
efficient if we first process equalities, then orider and, finally, all other
facts.  To make this easy, we store unprocessed facts as 'RawFacts' instead
of just using [Fact].

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

data RawFacts = RawFacts { rawEqFacts  :: [Fact]
                         , rawLeqFacts :: [Fact]
                         , rawFacts    :: [Fact]
                         }

noRawFacts :: RawFacts
noRawFacts = RawFacts { rawEqFacts  = []
                      , rawLeqFacts = []
                      , rawFacts    = []
                      }

insertRawFact :: Fact -> RawFacts -> RawFacts
insertRawFact f fs = case propPred f of
                       Eq  -> fs { rawEqFacts  = f : rawEqFacts fs }
                       Leq -> fs { rawLeqFacts = f : rawLeqFacts fs }
                       _   -> fs { rawFacts    = f : rawFacts fs }

oneRawFact :: Fact -> RawFacts
oneRawFact f = insertRawFact f noRawFacts

appendRawFacts :: RawFacts -> RawFacts -> RawFacts
appendRawFacts fs1 fs2 =
  RawFacts { rawEqFacts  = rawEqFacts  fs1 ++ rawEqFacts  fs2
           , rawLeqFacts = rawLeqFacts fs1 ++ rawLeqFacts fs2
           , rawFacts    = rawFacts    fs1 ++ rawFacts    fs2
           }

getRawFact :: RawFacts -> Maybe (Fact, RawFacts)
getRawFact fs =
  case rawEqFacts fs of
    e : es -> return (e, fs { rawEqFacts = es })
    []     -> case rawLeqFacts fs of
                l : ls -> return (l, fs { rawLeqFacts = ls })
                []     -> case rawFacts fs of
                            o : os -> return (o, fs { rawFacts = os })
                            []     -> Nothing

rawFactsFromList :: [Fact] -> RawFacts
rawFactsFromList = foldr insertRawFact noRawFacts

rawFactsToList :: RawFacts -> [Fact]
rawFactsToList fs = rawEqFacts fs ++ rawLeqFacts fs ++ rawFacts fs
--------------------------------------------------------------------------------



{- A collection of facts. Equalities are normalized to form a substitution,
and we inforce the invariant that this substitution is always applied to
the remaining facts. Also, ordering predicates are grouped into a separate
structire, the order model. -}

data Facts = Facts { facts    :: Props Fact -- Excluding equality and order
                   , factsEq  :: Subst      -- Normalized equalities
                   , factsLeq :: LeqFacts   -- Normalized order
                   }

factsToList :: Facts -> [Fact]
factsToList fs = substToFacts (factsEq fs) ++
                 leqFactsToList (factsLeq fs) ++
                 propsToList (facts fs)

noFacts :: Facts
noFacts = Facts { facts = noProps, factsEq = emptySubst, factsLeq = noLeqFacts }

insertFact :: Fact -> Facts -> Maybe (RawFacts,Facts)
insertFact f fs = case insertImpFact (impFact (factsEq fs) f) fs of
                    Inconsistent -> Nothing
                    AlreadyKnown -> Just (noRawFacts, fs)
                    Improved f1  -> Just (oneRawFact f1, fs)
                    Added xs fs1 -> Just (xs, fs1)


{- NOTE: This function assumes that the substition from the facts has
already been applied to the new fact.  It can be used as an optimization to
avoid applying the substitution twice. -}

insertImpFact :: Fact -> Facts -> AddFact
insertImpFact f fs =
  case factProp f of
    Prop Eq  [s,t] -> eqAddFact  (factProof f) s t fs
    Prop Leq [s,t] -> leqAddFact (factProof f) s t fs
    _ | impossible (factProp f) -> Inconsistent
    _ ->
      case solve (facts fs) (factProp f) of
        Just _ -> AlreadyKnown

        -- XXX: Modify "implied" to generate RawFacts directly.
        _      -> Added (rawFactsFromList (implied fs f))
                        fs { facts = insertProps f (facts fs) }
  where
  -- XXX: It would be nicer to make this less ad-hoc.
  impossible (Prop Mul [Num x _, _, Num y _]) = isNothing (divide y x)
  impossible (Prop Exp [Num x _, _, Num y _]) = isNothing (descreteLog y x)
  impossible (Prop Exp [_, Num x _, Num y _]) = isNothing (descreteRoot y x)
  impossible _ = False


{- 'addFact' is simillar to 'insertFact' but it returns a bit more detail
about what happened.  In particular, if the fact is actually to be added
to the collection, we also compute a set of additional facts that follow
from combining the existing facts with the new one. -}

data AddFact = Inconsistent
             | AlreadyKnown
             | Improved Fact
             | Added RawFacts Facts     -- additional facts, new set

addFact :: Fact -> Facts -> AddFact
addFact fact0 cur_known =
  let (fact,changed) = impFactChange (factsEq cur_known) fact0
  in if changed
        then Improved fact
        else insertImpFact fact cur_known

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

addFactsTrans' :: Facts -> RawFacts -> Maybe Facts
addFactsTrans' fs = foldM addFactTrans fs . rawFactsToList

addFactsTrans :: Facts -> RawFacts -> Maybe Facts
addFactsTrans fs facts0 =
  trace "Transitive facts" $
  case addFactsTrans' fs facts0 of
    Nothing -> trace "(nothing)" Nothing
    Just x  -> trace (show (pp x)) $ Just x



{- The function 'goalToFact' is used when we attempt to solve a new goal
in terms of already existing goals. -}
goalToFact :: Goal -> Fact
goalToFact g = Fact { factProof = ByAsmp (goalName g), factProp = goalProp g }

assumeGoals :: MonadPlus m => [Goal] -> Facts -> m Facts
assumeGoals as bs = liftMb
                  $ addFactsTrans bs
                  $ rawFactsFromList
                  $ map goalToFact as

--------------------------------------------------------------------------------

{- A part of the solver's state keeps track of the current set of known facts,
and the goals that still need to be solved. -}

data SolverProps = SolverProps { given :: Facts, wanted :: Props Goal }

noSolverProps :: SolverProps
noSolverProps = SolverProps { given = noFacts, wanted = noProps }

insertGiven :: Fact -> SolverProps -> Maybe (RawFacts,SolverProps)
insertGiven g ps = do (new,gs) <- insertFact g (given ps)
                      return (new, ps { given = gs })

insertWanted :: Goal -> SolverProps -> SolverProps
insertWanted w ps = ps { wanted = insertProps w (wanted ps) }



{-------------------------------------------------------------------------------
Proofs and Theorems
-------------------------------------------------------------------------------}

data Theorem  = EqRefl      -- forall a.                        a = a
              | EqSym       -- forall a b.   (a = b)         => b = a
              | EqTrans     -- forall a b c. (a = b, b = c)  => a = c
              | Cong Pred   -- forall xs ys. (xs = ys, F xs) => F ys

              | LeqRefl     -- forall a.                         a <= a
              | LeqAsym     -- forall a b.   (a <= b, b <= a) => a = b
              | LeqTrans    -- forall a b c. (a <= b, b <= c) => a <= c
              | Leq0        -- forall a.                         0 <= a

              | DefAdd Integer Integer Integer
              | DefMul Integer Integer Integer
              | DefExp Integer Integer Integer
              | DefLeq Integer Integer

              | AddLeq
              | MulLeq
              | ExpLeq1
              | ExpLeq2
              | Add0 | Mul0 | Mul1 | Root0 | Root1 | Log1
              | AddComm | MulComm
              | SubL | SubR | DivL | DivR | Root | Log
              | MulGrowL | MulGrowR | ExpGrow
              | AddAssoc | MulAssoc | AddMul | MulExp | ExpAdd | ExpMul
              | AddAssocSym | MulAssocSym | AddMulSym
              | MulExpSym | ExpAddSym | ExpMulSym
              | FunAdd | FunMul | FunExp
                deriving Show

data Proof    = ByAsmp EvVar
              | Using Theorem [Term] [Proof]   -- Instantiation, sub-proofs
                deriving Show

byRefl :: Term -> Proof
byRefl t = Using EqRefl [t] []

isRefl :: Proof -> Bool
isRefl (Using EqRefl _ _) = True
isRefl _ = False

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


byLeqDef :: Integer -> Integer -> Proof
byLeqDef x y = Using (DefLeq x y) [] []

byLeqRefl :: Term -> Proof
byLeqRefl t = Using LeqRefl [t] []

byLeqTrans :: Term -> Term -> Term -> Proof -> Proof -> Proof
byLeqTrans _ _ _ (Using LeqRefl _ _) p = p
byLeqTrans _ _ _ p (Using LeqRefl _ _) = p
byLeqTrans t1 t2 t3 p1 p2 = Using LeqTrans [t1,t2,t3] [p1,p2]

byLeqAsym :: Term -> Term -> Proof -> Proof -> Proof
byLeqAsym t1 t2 p1 p2 = Using LeqAsym [t1,t2] [p1,p2]

byLeq0 :: Term -> Proof
byLeq0 t = Using Leq0 [t] []


-- (x1 = y1, x2 = y2, P x1 x2) => P y1 y2
byCong :: Pred -> [Term] -> [Proof] -> Proof -> Proof
byCong _ _ qs q | all isRefl qs = q

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

{-------------------------------------------------------------------------------
Results of Entailement
-------------------------------------------------------------------------------}

{- | The entailment function may return one of three possible answers,
informally corresponding to ``certainly not'', ''not in its current form'',
and ''(a qualified) yes''. -}
data Answer = NotForAny | NotForAll | YesIf [Goal] Proof

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

data PassResult = PassResult { solvedWanted :: [(EvVar,Proof)]
                             , newGoals     :: [Goal]
                             , newFacts     :: RawFacts
                             , consumed     :: Bool
                             }

noChanges :: PassResult
noChanges = PassResult { solvedWanted = []
                       , newGoals     = []
                       , newFacts     = noRawFacts
                       , consumed     = False
                       }



{-------------------------------------------------------------------------------
Adding a New Assumption (given)

When we add a new assumption to an inert set we check for ``interactions''
with the existing assumptions by using the entailment function.
-------------------------------------------------------------------------------}

addGiven  :: Fact -> InertProps -> TCN PassResult
addGiven g props =
  case addFact g (given props) of

    Inconsistent  -> mzero
    AlreadyKnown  -> return noChanges { consumed = True }
    Improved fact -> return noChanges { consumed = True
                                      , newFacts = oneRawFact fact
                                      }

{- We don't add the new fact to the inerts yet because, in the context of GHC,
there might be another pass that might want to have a go at the goal.

When a new fact is added to the system, we need to restart any existing
goal, because they might be solvable using the new fact.  Currently,
this is done in our top level solver, when it encounters a non-consumed
given.  It is important to make sure that GHC does the same.  If
not, we can simulate the same behavior when we translate from this
representation to GHC's.
-}

    Added new _ -> return
      PassResult { newGoals      = []
                 , newFacts      = new
                 , solvedWanted  = []
                 , consumed      = False
                 }


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

addWanted :: Goal -> InertProps -> TCN PassResult
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
            , newFacts      = noRawFacts
            , consumed      = True
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

                   return PassResult
                     { solvedWanted = solved
                     , newGoals     = new
                     , newFacts     = noRawFacts
                     , consumed     = False
                     }

  where
  wantedList        = propsToList (wanted props)

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
  where msg = text "Entails?" $$ nest 2 (vcat (map pp (propsToList (facts ps)))
                                      $$ text "-----------------"
                                      $$ pp p
                                        )

entails ps p =
  do attempt1 <- entailsSimple ps p
     case attempt1 of
       NotForAll
         | improvable ->    -- Is there room for improvement?
         case addFactsTrans ps (oneRawFact (goalToFact p)) of

           -- The new goal contradicts the given assumptions.
           Nothing -> return NotForAny

           {- New facts!  We consider only the equalities. -}
           Just (Facts { factsEq = su1 }) ->
             do eqns <- mapM newGoal $ map factProp $ substToFacts su1
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




{- Proprties of the Entailment Function.

The following two functions state some properties of the entailment
function.  It would be nice to try to prove that they hold.
-}


-- | Adding more assumptions cannot make things less contradictory
entails_any_prop :: Facts -> Goal -> Fact -> TCN ()
entails_any_prop ps q p =
  do res <- entails ps q
     case res of
       NotForAny ->
         case addFactTrans ps p of
           Nothing -> return ()
           Just ps1 -> (guard . isNotForAny) =<< entails ps1 q
       _         -> return ()


-- | Dropping assumptions cannot make things more contradictory or more defined.
enatils_all_prop :: Fact -> Facts -> Goal -> TCN ()
enatils_all_prop p ps q =
  case addFactTrans ps p of
    Just ps1 -> do ans <- entails ps1 q
                   case ans of
                     NotForAll -> (guard . isNotForAll) =<< entails ps q
                     _         -> return ()
    _ -> return ()


{- Substitutions With Evidence -}

{- The proof asserts that the variable (as a term) is equal to the term. -}
newtype Subst  = Subst (M.Map Var (Term, Proof))

substToFacts :: Subst -> [Fact]
substToFacts (Subst m) = [ Fact { factProp  = Prop Eq [Var x, t]
                                , factProof = ev
                                } | (x,(t,ev)) <- M.toList m ]

substDom :: Subst -> [Var]
substDom (Subst m) = M.keys m

emptySubst :: Subst
emptySubst = Subst M.empty

isEmptySubst :: Subst -> Bool
isEmptySubst (Subst m) = M.null m

singleSubst :: Var -> Term -> Proof -> Subst
singleSubst x t e = Subst (M.singleton x (t,e))

compose :: Subst -> Subst -> Subst
compose s2@(Subst m2) (Subst m1) = Subst (M.union (M.mapWithKey ap2 m1) m2)
  where ap2 x (t,p1) = let (t2,p2) = apSubst s2 t
                       in (t2, byTrans (Var x) t t2 p1 p2)

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
eqBindVar eq x t fs = Added RawFacts { rawEqFacts  = []
                                     , rawLeqFacts = leqRestart
                                     , rawFacts    = changed
                                     }
                            Facts { factsEq   = compose su (factsEq fs)
                                  , factsLeq  = leqModel
                                  , facts     = others
                                  }

  where
  {-No need for an "occurs" check because the terms are simple (no recursion)-}
  su                     = singleSubst x t eq

  (leqRestart, leqModel) = case leqExtract (Var x) (factsLeq fs) of
                             Nothing      -> ([], factsLeq fs)
                             Just (lfs,m) -> (map (impFact su) lfs, m)

  (changed, others)      = mapExtract improve (facts fs)

  improve fact           = case impFactChange su fact of
                             (_,False) -> Nothing
                             (fact1,_) -> Just fact1



{- The returned proof asserts that the original term and the term with
the substitution applied are equal.
For example: apSubst [ ("x", 3, ev) ] "x" == (3, ev)

Here we work with only very simple proofs.  For more complex terms,
the proofs would also need to use congruence.
-}

apSubst :: Subst -> Term -> (Term, Proof)
apSubst (Subst m) (Var x) | Just res <- M.lookup x m  = res
apSubst _ t = (t, byRefl t)

{- Given a goal, return a new goal, and a proof which
solves the old goal in terms of the new one.
We return 'Nothing' if nothing got improved. -}
impGoal :: Subst -> Goal -> TCN (Maybe (Goal, Proof))
impGoal su p
  | isEmptySubst su || propArgs p == ts  = return Nothing
  | otherwise = do g <- newGoal (Prop (propPred p) ts)
                   return $ Just (g, byCong (propPred p)
                                       (ts ++ propArgs p)
                                       (zipWith3 bySym (propArgs p) ts evs)
                                       (ByAsmp (goalName g)))
  where (ts,evs) = unzip $ map (apSubst su) (propArgs p)

-- If "A : P x", and "B : x = 3", then "ByCong P [B] A : P 3"
impFact :: Subst -> Fact -> Fact
impFact su p = fst (impFactChange su p)

-- If "A : P x", and "B : x = 3", then "ByCong P [B] A : P 3"
impFactChange :: Subst -> Fact -> (Fact, Bool)
impFactChange su p = ( p { factProof = byCong (propPred p) (propArgs p ++ ts)
                                                           evs (factProof p)
                         , factProp  = Prop (propPred p) ts
                         }

                     -- Indicates if something changed.
                     , not (all isRefl evs)
                     )
  where (ts,evs) = unzip $ map (apSubst su) (propArgs p)



{-------------------------------------------------------------------------------
Reasoning About Order
-------------------------------------------------------------------------------}

{- To reason about order, we store the information about related terms
as a graph: the nodes are terms, and the edges are labelled with proofs,
providing evidence of the relation between the terms.
-}


data LeqEdge = LeqEdge { leProof :: Proof, leTarget :: Term }
               deriving Show

instance Eq LeqEdge where
  x == y  = leTarget x == leTarget y

instance Ord LeqEdge where
  compare x y = compare (leTarget x) (leTarget y)

data LeqEdges = LeqEdges { lnAbove :: S.Set LeqEdge -- proof: here   <= above
                         , lnBelow :: S.Set LeqEdge -- proof: bellow <= here
                         } deriving Show

leqNodeFacts :: Term -> LeqEdges -> [Fact]
leqNodeFacts x es = toFacts lnBelow lowerFact ++ toFacts lnAbove upperFact
  where
  toFacts list f = map f $ S.toList $ list es

  upperFact f    = Fact { factProp  = Prop Leq [x, leTarget f]
                        , factProof = leProof f
                        }

  lowerFact f    = Fact { factProp  = Prop Leq [leTarget f, x]
                        , factProof = leProof f
                        }

noLeqEdges :: LeqEdges
noLeqEdges = LeqEdges { lnAbove = S.empty, lnBelow = S.empty }

newtype LeqFacts = LM (M.Map Term LeqEdges)
                   deriving Show

noLeqFacts :: LeqFacts
noLeqFacts = LM M.empty

leqFactsToList :: LeqFacts -> [Fact]
leqFactsToList (LM m) =
  do (from,edges) <- M.toList m
     edge         <- S.toList (lnAbove edges)
     let to = leTarget edge
     guard (not (triv from to))
     return Fact { factProof = leProof edge, factProp = Prop Leq [ from, to ] }

  where triv (Num {}) (Num {}) = True
        triv (Num 0 _) _       = True
        triv _       _         = False



leqImmAbove :: LeqFacts -> Term -> S.Set LeqEdge
leqImmAbove (LM m) t = case M.lookup t m of
                         Just edges -> lnAbove edges
                         Nothing    -> S.empty


leqReachable :: LeqFacts -> Term -> Term -> Maybe Proof
leqReachable m smaller larger =
  search S.empty (S.singleton LeqEdge { leProof  = byLeqRefl smaller
                                      , leTarget = smaller })
  where
  search visited todo =
    do (LeqEdge { leProof = proof, leTarget = term }, rest) <- S.minView todo
       if term == larger
          then return proof
          else let updProof e = e { leProof = byLeqTrans
                                                smaller
                                                term
                                                (leTarget e)
                                                proof
                                                (leProof e) }

                   new     = S.mapMonotonic updProof (leqImmAbove m term)
                   vis     = S.insert term visited
                   notDone = S.filter (not . (`S.member` vis) . leTarget)
          in search vis (notDone new `S.union` notDone rest)




{-

This diagram illustrates what we do when we link two nodes (leqLink).

We start with a situation like on the left, and we are adding an
edge from L to U.  The final result is illustrated on the right.

   Before    After

     a         a
    /|        /
   / |       /
  U  |      U\
  |  L        \L
  | /         /
  |/         /
  d         d

L: lower
U: upper
a: a member of "lnAbove uedges"  (uus)
d: a member of "lnBelow ledges"  (lls)
-}



leqLink :: Proof -> (Term,LeqEdges) -> (Term,LeqEdges) -> LeqFacts ->
                                                  (LeqEdges,LeqEdges,LeqFacts)

leqLink proof (lower, ledges) (upper, uedges) (LM m) =

  let uus         = S.mapMonotonic leTarget (lnAbove uedges)
      lls         = S.mapMonotonic leTarget (lnBelow ledges)

      newLedges   = ledges { lnAbove =
                               S.insert (LeqEdge { leProof  = proof
                                                 , leTarget = upper
                                                 })
                               $ S.filter (not . (`S.member` uus) . leTarget)
                               $ lnAbove ledges
                           }
      newUedges   = uedges { lnBelow =
                               S.insert (LeqEdge { leProof  = proof
                                                 , leTarget = lower
                                                 })
                               $ S.filter (not . (`S.member` lls) . leTarget)
                               $ lnBelow uedges
                           }

{- The "undefined" in 'del' is OK because the proofs are not used in the
comparison and the set API seems to lack a function to get the same behavior.
Note that filter-ing is a little different because it has to traverse the
whole set while here we stop as soon as we found the element that is
to be removed. -}

      del x       = S.delete LeqEdge { leTarget = x, leProof = undefined }


      adjAbove    = M.adjust (\e -> e { lnAbove = del upper (lnAbove e) })
      adjBelow    = M.adjust (\e -> e { lnBelow = del lower (lnBelow e) })
      fold f xs x = S.fold f x xs

  in ( newLedges
     , newUedges
     , LM $ M.insert lower newLedges
          $ M.insert upper newUedges
          $ fold adjAbove lls
          $ fold adjBelow uus
            m
     )

leqInsNode :: Term -> LeqFacts -> (LeqEdges, LeqFacts)
leqInsNode t model@(LM m0) =
  case M.splitLookup t m0 of
    (_, Just r, _)  -> (r, model)
    (left, Nothing, right) ->
      let new           = noLeqEdges
          ans1@(es1,m1) = ( new, LM (M.insert t new m0) )
      in case t of
           Var _ ->
             -- link to 0
             let zero         = num 0
                 (zes,zm)     = leqInsNode zero m1    -- Should not modify es1
                 (_, es2, m2) = leqLink (byLeq0 t) (zero,zes) (t,es1) zm
             in (es2, m2)
           Num m _ ->
             -- link to a smaller constnat, if any
             let ans2@(es2, m2) =
                   case toNum M.findMax left of
                     Nothing -> ans1
                     Just (n,l)  ->
                       let (_,x,y) = leqLink (byLeqDef n m) l (t,es1) m1
                       in (x,y)
             -- link to a larger constant, if any
             in case toNum M.findMin right of
                  Nothing -> ans2
                  Just (n,u)  ->
                    let (x,_,y) = leqLink (byLeqDef m n) (t,es2) u m2
                    in (x,y)

  where
  toNum f x = do guard (not (M.null x))
                 let r = f x
                 case fst r of
                   Num n _ -> return (n,r)
                   _       -> Nothing


leqAddFact :: Proof -> Term -> Term -> Facts -> AddFact
leqAddFact proof t1 t2 fs =
  let m0        = factsLeq fs
      (n1,m1)   = leqInsNode t1 m0
      (n2,m2)   = leqInsNode t2 m1

  in case leqReachable m2 t2 t1 of

       Nothing ->

         case leqReachable m2 t1 t2 of
           Nothing -> let (_,_,m3) = leqLink proof (t1,n1) (t2,n2) m2
                      in Added noRawFacts { rawFacts = propsToList (facts fs) }
                               fs { factsLeq = m3, facts = noProps }
           Just _  -> AlreadyKnown

       {- We know the opposite: we don't add the fact
          but propose an equality instead. -}
       Just pOp -> Improved $
         Fact { factProof = byLeqAsym t1 t2 proof pOp
              , factProp  = Prop Eq [t1,t2]
              }


leqFactsAffectedBy :: LeqFacts -> Subst -> Bool
leqFactsAffectedBy (LM m) = any affects . substDom
  where affects x = case M.lookup (Var x) (fst (M.split (num 0) m)) of
                      Nothing -> False
                      _       -> True

leqProve :: LeqFacts -> Term -> Term -> Maybe Proof
leqProve model s t =
  let (_,m1) = leqInsNode s model
      (_,m2) = leqInsNode t m1
  in leqReachable m2 s t


{- Remove the term from the model, and return the facts immediately
associated with ot.

This is useful when we want to improve a term: we remove it from the model,
improve the associated facts, and then add them back.
-}
leqExtract :: Term -> LeqFacts -> Maybe ([Fact], LeqFacts)
leqExtract term (LM m) =
  case M.updateLookupWithKey (\_ _ -> Nothing) term m of
    (Nothing, _)  -> Nothing
    (Just es, m1) -> Just
      ( leqNodeFacts term es
      , LM $ fold adjAbove (nodes lnBelow es)
           $ fold adjBelow (nodes lnAbove es) m1
      )
  where
  del         = S.delete LeqEdge { leTarget = term, leProof = undefined }
  adjAbove    = M.adjust (\e -> e { lnAbove = del (lnAbove e) })
  adjBelow    = M.adjust (\e -> e { lnBelow = del (lnBelow e) })
  nodes f es  = S.mapMonotonic leTarget (f es)
  fold f xs x = S.fold f x xs

leqContains :: LeqFacts -> Term -> Bool
leqContains (LM m) t = case M.lookup t m of
                         Nothing -> False
                         Just _  -> True

--------------------------------------------------------------------------------

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

cmpType :: Xi -> Xi -> Ordering
cmpType = compare

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

data SolverS = SolverS
  { ssTodoFacts :: RawFacts
  , ssTodoGoals :: [Goal]
  , ssSolved    :: [(EvVar,Proof)]
  , ssInerts    :: InertProps
  }

initSolverS :: SolverS
initSolverS = SolverS
  { ssTodoGoals = []
  , ssTodoFacts = noRawFacts
  , ssSolved    = []
  , ssInerts    = noSolverProps
  }


getFact :: SolverS -> Maybe (Fact, SolverS)
getFact s = case getRawFact (ssTodoFacts s) of
              Nothing     -> Nothing
              Just (f,fs) -> Just (f, s { ssTodoFacts = fs })

getGoal :: SolverS -> Maybe (Goal, SolverS)
getGoal s = case ssTodoGoals s of
              []     -> Nothing
              g : gs -> Just (g, s { ssTodoGoals = gs })

addSolved :: [(EvVar,Proof)] -> SolverS -> SolverS
addSolved [] s = s
addSolved xs s = s { ssSolved = xs ++ ssSolved s
                   , ssInerts = is { wanted = filterProps keep (wanted is) }
                   }
  where is     = ssInerts s
        keep p = not (goalName p `elem` map fst xs)

nextState :: PassResult -> SolverS -> SolverS
nextState r s = addSolved (solvedWanted r)
                s { ssTodoFacts = appendRawFacts (newFacts r) (ssTodoFacts s)
                  , ssTodoGoals = newGoals r ++ ssTodoGoals s
                  }

restartGoals :: SolverS -> SolverS
restartGoals s = s { ssTodoGoals = propsToList (wanted is) ++ ssTodoGoals s
                   , ssInerts    = is { wanted = noProps }
                   }
  where is = ssInerts s

addWorkItems :: SolverS -> String -> Int -> Maybe SolverS
addWorkItems is r s = fst `fmap` runTCN (addWorkItemsM is) r s

-- The final state should have empty 'todo*' queues.
addWorkItemsM :: SolverS -> TCN SolverS

addWorkItemsM ss0 =
  case getFact ss0 of
    Just (fact, ss1) ->
      do r <- addGiven fact (ssInerts ss1)
         let ss2 = nextState r ss1
         if consumed r
            then addWorkItemsM ss2
            else do (new,is) <- liftMb $ insertGiven fact $ ssInerts ss2
                    addWorkItemsM $ restartGoals
                      ss2 { ssTodoFacts = appendRawFacts new (ssTodoFacts ss2)
                          , ssInerts    = is
                          }

    Nothing ->
      case getGoal ss0 of
       Just (goal, ss1) ->
         do r <- addWanted goal (ssInerts ss1)
            let ss2 = nextState r ss1
            addWorkItemsM $
              if consumed r
                then ss2
                else ss2 { ssInerts = insertWanted goal (ssInerts ss2) }

       Nothing -> return ss0

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
descreteRoot x0 root = search 0 x0
  where
  search from to = let x = from + div (to - from) 2
                       a = x ^ root
                   in case compare a x0 of
                        EQ              -> Just x
                        LT | x /= from  -> search x to
                        GT | x /= to    -> search from x
                        _               -> Nothing

descreteLog :: Integer -> Integer -> Maybe Integer
descreteLog 0  _  = Just 0
descreteLog x0 base | base == x0  = Just 1
descreteLog x0 base = case divMod x0 base of
                         (x,0) -> fmap (1+) (descreteLog x base)
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

instance PP Var where
  pp (V x) = text x

instance PP Term where
  pp (Var x)    = pp x
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
  pp is = pp (given is) $$ pp (wanted is)

instance PP Facts where
  pp fs = vcat (map pp (factsToList fs))

instance PP LeqFacts where
  pp = vcat . map pp . leqFactsToList


{-------------------------------------------------------------------------------
Misc.
-------------------------------------------------------------------------------}

instance Eq Var where
  V x == V y  = eqType x y

instance Ord Var where
  compare (V x) (V y) = cmpType x y

-- | Choce an element from a list in all possible ways.
choose :: [a] -> [(a,[a])]
choose []     = []
choose (x:xs) = (x,xs) : [ (y, x:ys) | (y,ys) <- choose xs ]

liftMb :: MonadPlus m => Maybe a -> m a
liftMb mb = case mb of
              Nothing -> mzero
              Just a  -> return a

ppTrace :: Doc -> a -> a
ppTrace d = trace (show d)

gTrace :: Doc -> Bool
gTrace d = ppTrace d False

#include "TcTypeNatsRules.hs"


