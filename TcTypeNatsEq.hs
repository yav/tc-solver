{- | This module defines idempotent substitutions with evidence.
This means that each binding in the substitution has an associated proof
explaining why the variable is equal to the term.  As a result, when we
apply a substitution to a term, we can also compute a proof that that the
new term is equal to the original one.
-}
module TcTypeNatsEq
  ( -- * Using
    Subst
  , apply
    -- * Constructing
  , identity
  , singleton
  , compose
    -- * Observing
  , domain
  , isIdentity
  , toFacts
  ) where

import TcTypeNatsBase
import qualified Data.Map as M

-- | Substitutions with evidence.
newtype Subst = Subst (M.Map Var (Proof,Term))

-- | A list of facts that is equivalent to the substitution.
toFacts :: Subst -> [Fact]
toFacts (Subst m) = [ Fact { factProp  = Prop Eq [Var x, t]
                           , factProof = ev
                           } | (x,(ev,t)) <- M.toList m ]

-- | The list contains the variables that are affected by the substitution.
domain :: Subst -> [Var]
domain (Subst m) = M.keys m

-- | The identity substitution does not affect any variables.
identity :: Subst
identity = Subst M.empty

-- | Check if this is the identity substitution.
isIdentity :: Subst -> Bool
isIdentity (Subst m) = M.null m

-- | A substitution that binds a variable to a term and leaves all other
-- variables unchanged.
singleton :: Proof -> Var -> Term -> Subst
singleton _ x (Var y)
  | x == y        = identity
singleton e x t   = Subst (M.singleton x (e,t))

-- | Compose two substitutions.
-- @apply (compose s2 s1) = apply s2 . apply s1@
compose :: Subst -> Subst -> Subst
compose s2@(Subst m2) (Subst m1) = Subst (M.union (M.mapWithKey ap2 m1) m2)
  where ap2 x (p1,t) = let (p2,t2) = apply s2 t
                       in (byTrans (Var x) t t2 p1 p2, t2)

{-| Apply a substitution to a term.
The returned proof asserts that the original term is equal to the result.
For example: @apply (singelton ev x 3) x == (ev, 3)@ -}

apply :: Subst -> Term -> (Proof,Term)
apply (Subst m) (Var x)
  | Just res <- M.lookup x m  = res
apply _ t                     = (byRefl t, t)

{- NOTE: Here we work with very simple proofs.  For more complex terms,
the proofs would also need to use congruence.
-}




