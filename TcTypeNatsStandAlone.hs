{- | Definitions of basic types for standalone testing. -}
module TcTypeNatsStandAlone
  ( Var, EvVar
  , pprVar, pprEvVar
  , TCN
  , newEvVar
  , impossibleGoal
  , impossibleFact

  , runTCN      -- only in standalone mode
  , strVar
  , strEvVar
  ) where

import Text.PrettyPrint

newtype Var   = V String
                deriving (Eq,Ord)

newtype EvVar = EvVar String
                deriving (Eq,Ord)

-- ???
pprVar :: Var -> Doc
pprVar (V x) = text x

pprEvVar :: EvVar -> Doc
pprEvVar (EvVar x) = text x


newtype TCN a = T (String -> Int -> Maybe (a,Int))

instance Functor TCN where
  fmap f m = do x <- m
                return (f x)

instance Monad TCN where
  return x  = T $ \_ s -> return (x,s)
  T m >>= f = T $ \r s -> do (a,s1) <- m r s
                             let T m1   = f a
                             m1 r $! s1

newEvVar :: TCN EvVar
newEvVar = T $ \r s ->
  do let s1 = s + 1
     s1 `seq` Just (EvVar (r ++ "_" ++ show s), s1)

-- XXX
impossibleGoal :: TCN a
impossibleGoal = T (\_ _ -> Nothing)

-- XXX
impossibleFact :: TCN a
impossibleFact = impossibleGoal


--------------------------------------------------------------------------------
-- These are not part of the interface, they are just part of
-- the standalone implementation.

strVar :: String -> Var
strVar = V

strEvVar :: String -> EvVar
strEvVar x = EvVar x

runTCN :: TCN a -> String -> Int -> Maybe (a,Int)
runTCN (T a) = a


