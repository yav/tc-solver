{- Substitutions With Evidence -}
module TcTypeNatsEq where

import TcTypeNatsBase
import qualified Data.Map as M

{- The proof asserts that the variable (as a term) is equal to the term. -}
newtype Subst = Subst (M.Map Var (Term, Proof))

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

{- The returned proof asserts that the original term and the term with
the substitution applied are equal.
For example: apSubst [ ("x", 3, ev) ] "x" == (3, ev)

Here we work with only very simple proofs.  For more complex terms,
the proofs would also need to use congruence.
-}

apSubst :: Subst -> Term -> (Term, Proof)
apSubst (Subst m) (Var x) | Just res <- M.lookup x m  = res
apSubst _ t = (t, byRefl t)


