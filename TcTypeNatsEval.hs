{-| This module defines the inverse functions used for simplifying
propositions using concrete natural numbers.
-}

module TcTypeNatsEval where

import Data.Maybe(fromMaybe)

-- | Subtract two natural numbers.
minus :: Integer -> Integer -> Maybe Integer
minus x y = if x >= y then Just (x - y) else Nothing

-- | Compute the exact root of two natural numbers.
-- The second argument specifies which root we are computing.
discreteRoot :: Integer -> Integer -> Maybe Integer
discreteRoot x0 root = search 0 x0
  where
  search from to = let x = from + div (to - from) 2
                       a = x ^ root
                   in case compare a x0 of
                        EQ              -> Just x
                        LT | x /= from  -> search x to
                        GT | x /= to    -> search from x
                        _               -> Nothing


-- | Compute the logarithm of a number in the given base, rounded down to the
-- closest integer.  The boolean indicates if we the result is exact
-- (i.e., True means no rounding happened, False means we rounded down).
-- The logarithm base is the second argument.
genLog :: Integer -> Integer -> Maybe (Integer, Bool)
genLog x 0    = if x == 1 then Just (0, True) else Nothing
genLog _ 1    = Nothing
genLog 0 _    = Nothing
genLog x base = Just (exactLoop 0 x)
  where
  exactLoop s i
    | i == 1     = (s,True)
    | i < base   = (s,False)
    | otherwise  =
        let s1 = s + 1
        in s1 `seq` case divMod i base of
                      (j,r)
                        | r == 0    -> exactLoop s1 j
                        | otherwise -> (underLoop s1 j, False)

  underLoop s i
    | i < base  = s
    | otherwise = let s1 = s + 1 in s1 `seq` underLoop s1 (div i base)



-- | Compute the exact logarithm of a natural number.
-- The logarithm base is the second argument.
logExact :: Integer -> Integer -> Maybe Integer
logExact x y = do (z,True) <- genLog x y
                  return z

-- | Compute the logarithm of a natural number, roundig down, if neccessary.
logRoundDown :: Integer -> Integer -> Maybe Integer
logRoundDown x y = fmap fst (genLog x y)

-- | Compute the logarithm of a natural number, roundig up, if neccessary.
logRoundUp :: Integer -> Integer -> Maybe Integer
logRoundUp x y = do (z,exact) <- genLog x y
                    if exact then return z else return (z + 1)




-- | Divide two natural numbers.
divide :: Integer -> Integer -> Maybe Integer
divide _ 0  = Nothing
divide x y  = case divMod x y of
                (a,0) -> Just a
                _     -> Nothing



--------------------------------------------------------------------------------


-- The functions bellow are for interval analysis.

-- | Natural numbers with a top infinity element. (No negative numbers!)
data InfNat = Nat Integer | Infinity  deriving (Show,Eq,Ord)

{- | Consider @x + y = z@.  This function computes a lower bound for @x@,
using the upper bound for @y@ and the lower bound for @z@. -}
subLower :: Integer -> InfNat -> Integer
subLower _     Infinity    = 0
subLower z_min (Nat max_y) = fromMaybe 0 (minus z_min max_y)

{- | Consider @x + y = z@.  This function computes an upper bound for @x@,
using the lower bound for @y@ and the upper bound for @z@. -}
subUpper :: InfNat -> Integer -> InfNat
subUpper Infinity _        = Infinity
subUpper (Nat max_z) min_y = Nat (fromMaybe 0 (minus max_z min_y))

{- | Consider @x * y = z@.  This function computes a lower bound for @x@,
using the upper bound for @y@ and the lower bound for @z@. -}
divLower :: Integer -> InfNat -> Integer
divLower 0 _        = 0
divLower _ Infinity = 1 -- if result is not 0, x must be at least 1
divLower z_min (Nat y_max)
  | y_max == 0 = 0   -- should have been improved.
  | otherwise  = case divMod z_min y_max of
                   (q,r) -> if r == 0 then q else q + 1

{- | Consider @x * y = z@.  This function computes an upper bound for @x@,
using the lower bound for @y@ and the upper bound for @z@. -}
divUpper :: InfNat -> Integer -> InfNat
divUpper Infinity _ = Infinity
divUpper (Nat z_max) y_min
  | y_min == 0 = Infinity
  | otherwise  = Nat (div z_max y_min)



{- | Consider @x ^ y = z@.  This function computes a lower bound for @y@,
using the upper bound for @x@ and the lower bound for @z@.
Example: logLower 5 (Nat 2) = 3, because y has to be at least 3,
         if we want @2^y >= 5@.
-}
logLower :: Integer -> InfNat -> Integer
logLower _ Infinity = 0
logLower z_min (Nat x_max) = fromMaybe 0 (logRoundUp z_min x_max)

{- | Consider @x ^ y = z@.  This function computes an upper bound for @y@,
using the lower bound for @x@ and the upper bound for @z@.
-}
logUpper :: InfNat -> Integer -> InfNat
logUpper Infinity _        = Infinity
logUpper (Nat z_max) x_min = maybe Infinity Nat (logRoundDown z_max x_min)


