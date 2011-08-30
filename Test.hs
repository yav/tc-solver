{-# LANGUAGE CPP #-}

module Test where

import Data.Maybe(catMaybes)
import Control.Monad(mzero)

type Xi = String

data Term = Var Xi | Num Integer (Maybe Xi)
            deriving Eq
data Op   = Add | Mul | Exp deriving Eq
data Prop = EqFun Op Term Term Term
          | Leq Term Term
          | Eq Term Term
            deriving Eq

instance Show Term where
  show (Var x)    = x
  show (Num x _)  = show x

instance Show Op where
  show Add = "+"
  show Mul = "*"
  show Exp = "^"

instance Show Prop where
  show (EqFun op t1 t2 t3)  = show t1 ++ " " ++ show op ++ " " ++ show t2
                              ++ " == " ++ show t3
  show (Eq x y)             = show x ++ " == " ++ show y
  show (Leq x y)            = show x ++ " <= " ++ show y

eqType :: Xi -> Xi -> Bool
eqType = (==)

num :: Integer -> Term
num n = Num n Nothing

minus :: Integer -> Integer -> Maybe Integer
minus x y = if x >= y then Just (x - y) else Nothing

descreteRoot :: Integer -> Integer -> Maybe Integer
descreteRoot root x0 = search 0 x0
  where
  search from to = let x = from + div (to - from) 2
                       a = x ^ root
                   in case compare a x0 of
                        EQ              -> Just x
                        LT | x /= from  -> search x to
                        GT | x /= to    -> search from x
                        _               -> Nothing

descreteLog :: Integer -> Integer -> Maybe Integer
descreteLog _    0   = Just 0
descreteLog base x0 | base == x0  = Just 1
descreteLog base x0 = case divMod x0 base of
                         (x,0) -> fmap (1+) (descreteLog base x)
                         _     -> Nothing

divide :: Integer -> Integer -> Maybe Integer
divide _ 0  = Nothing
divide x y  = case divMod x y of
                (a,0) -> Just a
                _     -> Nothing

choose :: [a] -> [(a,[a])]
choose []     = []
choose (x:xs) = (x,xs) : [ (y, x:ys) | (y,ys) <- choose xs ]

type Terms2 = (Term,Term)
type Terms3 = (Term,Term,Term)
data Props  = Props { pAdd :: [Terms3]
                    , pMul :: [Terms3]
                    , pExp :: [Terms3]
                    , pLeq :: [Terms2]
                    , pEq  :: [Terms2]   -- or just Subst?
                    }

noProps :: Props
noProps = Props [] [] [] [] []

addProp :: Prop -> Props -> Props
addProp prop props =
  case prop of
    EqFun Add t1 t2 t3 -> props { pAdd = (t1,t2,t3) : pAdd props }
    EqFun Mul t1 t2 t3 -> props { pMul = (t1,t2,t3) : pMul props }
    EqFun Exp t1 t2 t3 -> props { pExp = (t1,t2,t3) : pExp props }
    Leq t1 t2          -> props { pLeq = (t1,t2)    : pLeq props }
    Eq t1 t2           -> props { pEq  = (t1,t2)    : pEq props }





#include "TcTypeNatsRules.hs"




