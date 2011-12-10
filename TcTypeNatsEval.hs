{-| This module defines the inverse functions used for simplifying
propositions using concrete natural numbers.
-}

module TcTypeNatsEval where

-- | Subtract two natural numbers.
minus :: Integer -> Integer -> Maybe Integer
minus x y = if x >= y then Just (x - y) else Nothing

-- | Compute the exact root of two natural numbers.
-- The second argument specifies which root we are computing.
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

-- | Compute the exact logarithm of two natural numbers.
-- The logarithm base is the second argument.
descreteLog :: Integer -> Integer -> Maybe Integer
descreteLog 0  _  = Just 0
descreteLog x0 base | base == x0  = Just 1
descreteLog x0 base = case divMod x0 base of
                         (x,0) -> fmap (1+) (descreteLog x base)
                         _     -> Nothing

-- | Divide two natural numbers.
divide :: Integer -> Integer -> Maybe Integer
divide _ 0  = Nothing
divide x y  = case divMod x y of
                (a,0) -> Just a
                _     -> Nothing

