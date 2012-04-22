{- | Definitions of basic types for standalone testing. -}
module TcTypeNatsStandAlone
  ( Var, EvVar
  , pprVar, pprEvVar
  , TCN
  , newEvVar

  , runTCN      -- only in standalone mode
  , strVar
  , strEvVar
  ) where

import Text.PrettyPrint
import Control.Monad(MonadPlus(..))

newtype Var   = V String
                deriving (Eq,Ord)

newtype EvVar = EvVar String
                deriving (Eq,Ord)

-- only standalone
strVar :: String -> Var
strVar = V

-- only standalone
strEvVar :: String -> EvVar
strEvVar x = EvVar x

-- ???
pprVar :: Var -> Doc
pprVar (V x) = text x

pprEvVar :: EvVar -> Doc
pprEvVar (EvVar x) = text x


newtype TCN a = T { runTCN :: String -> Int -> Maybe (a,Int) }

instance Functor TCN where
  fmap f m = do x <- m
                return (f x)

instance Monad TCN where
  return x  = T $ \_ s -> return (x,s)
  T m >>= f = T $ \r s -> do (a,s1) <- m r s
                             let T m1   = f a
                             m1 r $! s1

instance MonadPlus TCN where
  mzero = T (\_ _ -> Nothing)
  mplus = error "mplus is unused"


newEvVar :: TCN EvVar
newEvVar = T $ \r s ->
  do let s1 = s + 1
     s1 `seq` Just (EvVar (r ++ "_" ++ show s), s1)




