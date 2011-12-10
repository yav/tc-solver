{-------------------------------------------------------------------------------
Collections of Entities with Propositions

Throughout the development we work with collections of propositions.
One way to represent such collections is, simply, to use linked lists.
However, because we often need to search for propositions
of a certain form, it is more convenient (and efficient) to group
propositions with the same predicate constructor together.
-------------------------------------------------------------------------------}

module TcTypeNatsProps where

import TcTypeNatsBase

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Either(partitionEithers)
import Text.PrettyPrint

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

{- | Apply a function to all memerbs, and keep only the ones that do
not change (i.e., the parameter returns 'Nothing').  The new values
of the members that did change are returned in a list. -}

mapExtract :: (Ord a, HasProp a) =>
              (a -> Maybe a) -> Props a -> ([a], Props a)
mapExtract f ps = case partitionEithers $ map apply $ propsToList ps of
                    (remains,changed) -> (changed, propsFromList remains)
  where apply x = case f x of
                    Nothing -> Left x
                    Just a  -> Right a

-- | Choce an element from a list in all possible ways.
choose :: [a] -> [(a,[a])]
choose []     = []
choose (x:xs) = (x,xs) : [ (y, x:ys) | (y,ys) <- choose xs ]

--------------------------------------------------------------------------------

instance (Ord a, PP a) => PP (Props a) where
  pp = vcat . map pp . propsToList


