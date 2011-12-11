module TcTypeNatsFacts where

import TcTypeNatsBase
import TcTypeNatsEq     as Subst
import qualified TcTypeNatsLeq as Leq
import TcTypeNatsProps  as Props

import Text.PrettyPrint

{- | A collection of facts. Equalities are normalized to form a substitution.
The substitution is always applied to the remaining facts.
Also, ordering predicates are grouped into a separate structure,
the order model. -}
data Facts = Facts { facts    :: Props Fact -- ^ Excluding equality and order
                   , factsEq  :: Subst      -- ^ Normalized equalities
                   , factsLeq :: Leq.Facts  -- ^ Normalized order
                   }

-- | Convert a collection of facts to a list.
factsToList :: Facts -> [Fact]
factsToList fs = Subst.toFacts (factsEq fs) ++
                 Leq.toList (factsLeq fs) ++
                 Props.toList (facts fs)

-- | An empty collection of facts.
noFacts :: Facts
noFacts = Facts { facts    = Props.empty
                , factsEq  = Subst.identity
                , factsLeq = Leq.empty
                }

instance PP Facts where
  pp fs = vcat (map pp (factsToList fs))


