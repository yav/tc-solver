module TcTypeNatsFacts where

import TcTypeNatsBase
import TcTypeNatsEq
import TcTypeNatsLeq
import TcTypeNatsProps

import Text.PrettyPrint

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

instance PP Facts where
  pp fs = vcat (map pp (factsToList fs))


