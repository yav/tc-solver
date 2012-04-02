{- | A collection of facts.  We use specialized representations for
some of the facts:  equalities are kept as a substitution
(see "TcTypeNatsEq"), while ordering facts are kept in
a graph (see "TcTypeNatsLeq"). -}
module TcTypeNatsFacts
  ( -- * Construction
    Facts
  , TcTypeNatsFacts.empty
  , addEqFact
  , addLeqFact
  , addOtherInertFact
  , AddFact(..)

  -- * Querying
  , getEqFacts
  , getLeqFacts
  , getOtherFacts
  , toList

    -- * Miscellaneous
  , improveFact
  ) where

import           TcTypeNatsBase
import qualified TcTypeNatsEq     as Subst
import           TcTypeNatsEq(Subst)
import qualified TcTypeNatsLeq    as Leq
import qualified TcTypeNatsProps  as Props
import           TcTypeNatsProps(Props)

import Text.PrettyPrint

{- | A collection of facts. The collection should satisfy the invariant that
equality facts are always reflected in the other facts of the collection. -}
data Facts = Facts { facts    :: Props Fact -- ^ Excluding equality and order
                   , factsEq  :: Subst      -- ^ Normalized equalities
                   , factsLeq :: Leq.Facts  -- ^ Normalized order
                   }

-- | Only the equality facts of the collection.
getEqFacts :: Facts -> Subst
getEqFacts = factsEq

-- | Only the ordering facts of the collection.
-- (Note that the return type refers to the Facts from "TcTypeNatsLeq".)
getLeqFacts :: Facts -> Leq.Facts
getLeqFacts = factsLeq

-- | The facts that are not equality or ordering.
getOtherFacts :: Facts -> Props Fact
getOtherFacts = facts

instance PP Facts where
  pp fs = vcat (map pp (toList fs))

-- | Convert a collection of facts to a list.
toList :: Facts -> [Fact]
toList fs = Subst.toFacts (factsEq fs) ++
            Leq.toList (factsLeq fs) ++
            Props.toList (facts fs)

-- | An empty collection of facts.
empty :: Facts
empty = Facts { facts    = Props.empty
              , factsEq  = Subst.identity
              , factsLeq = Leq.empty
              }


--------------------------------------------------------------------------------

{- | Apply a substitution to a fact.  Returns 'Nothing' if the substitution
does not change the fact. -}
improveFact :: Subst -> Fact -> Maybe Fact
improveFact su p = case impFactChange su p of
                     (_,False)  -> Nothing
                     (fact1,_)  -> Just fact1


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
  where (evs,ts) = unzip $ map (Subst.apply su) (propArgs p)


--------------------------------------------------------------------------------

-- | The result of trying to add a fact to a collection.
data AddFact
  = Inconsistent
  {- ^ The fact was not added because it would lead
  to an inconsistent collection of facts. -}

  | AlreadyKnown
  -- ^ The fact was not added because it was already known.

  | Improved [Fact]
  -- ^ The fact was not added because we found a better set of equivalent facts.

  | Added (Props Fact) Facts
  {- ^ The fact was added.  The first field contains additional facts that
  should be added.  The second field contains the new collection of facts.
  Note that sometimes the new collection may loose some facts because they
  were moved to the first field to be \"reconsidered\". -}



-- | Add an equality fact to a collection.
addEqFact :: Proof -> Term -> Term -> Facts -> AddFact
addEqFact eq t1 t2 fs =
  case (t1, t2) of
    _ | t1 == t2      -> AlreadyKnown

    (Num {}, Num {})  -> Inconsistent

    (Var x, Num {})   -> eqBindVar eq x t2 fs

    (Var x, _)
      | not (Leq.contains (factsLeq fs) t1) -> eqBindVar eq x t2 fs

    (_, Var y)        -> eqBindVar (bySym t1 t2 eq) y t1 fs


eqBindVar :: Proof -> Var -> Term -> Facts -> AddFact
eqBindVar eq x t fs = Added (Props.fromList (leqRestart ++ changed))
                            Facts { factsEq   = Subst.compose su (factsEq fs)
                                  , factsLeq  = leqModel
                                  , facts     = others
                                  }

  where
  {-No need for an "occurs" check because the terms are simple (no recursion)-}
  su                     = Subst.singleton eq x t

  (leqRestart, leqModel) = case Leq.extract (Var x) (factsLeq fs) of
                             Nothing      -> ([], factsLeq fs)
                             Just (lfs,m) -> (map (impFact su) lfs, m)

  (changed, others)      = Props.mapExtract (improveFact su) (facts fs)

-- | Add a fact about ordering to a colelction.
addLeqFact :: Proof -> Term -> Term -> Facts -> AddFact
addLeqFact ev t1 t2 fs =
  case Leq.addFact ev t1 t2 (factsLeq fs) of
    Leq.AlreadyKnown -> AlreadyKnown
    Leq.Improved f   -> Improved [f]
    Leq.Added ls     -> Added (facts fs) fs { factsLeq = ls
                                            , facts = Props.empty
                                            }

{- | Add a fact which is not about equality or ordering. -}
addOtherInertFact :: Fact -> Facts -> Facts
addOtherInertFact f fs = fs { facts = Props.insert f (facts fs) }


