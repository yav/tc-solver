{-------------------------------------------------------------------------------
Functions on natural numbers.
-------------------------------------------------------------------------------}
module TcTypeNatsEval where

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


