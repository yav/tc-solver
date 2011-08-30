{-# LANGUAGE CPP #-}

module Test where

import Data.Maybe(catMaybes)
import Data.List(unfoldr,union)
import Control.Monad(mzero)

type Xi = String

data Term = Var Xi | Num Integer (Maybe Xi)
            deriving (Eq,Ord)

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
    EqFun Add t1 t2 t3 -> props { pAdd = (t1,t2,t3) `ins` pAdd props }
    EqFun Mul t1 t2 t3 -> props { pMul = (t1,t2,t3) `ins` pMul props }
    EqFun Exp t1 t2 t3 -> props { pExp = (t1,t2,t3) `ins` pExp props }
    Leq t1 t2          -> props { pLeq = (t1,t2)    `ins` pLeq props }
    Eq t1 t2           -> props { pEq  = (t1,t2)    `ins` pEq props }
  where ins x [] = [x]
        ins x (y:ys)
          | x == y  = y : ys
          | x < y   = x : y : ys
          | otherwise = y : ins x ys

filterProp :: (Prop -> Bool) -> Props -> Props
filterProp p ps = Props
  { pAdd = filter (p3 (EqFun Add)) (pAdd ps)
  , pMul = filter (p3 (EqFun Mul)) (pMul ps)
  , pExp = filter (p3 (EqFun Exp)) (pExp ps)
  , pLeq = filter (p2 Leq)         (pLeq ps)
  , pEq  = filter (p2 Eq)          (pEq ps)
  }
  where p3 f (x,y,z) = p (f x y z)
        p2 f (x,y)   = p (f x y)


unionProps :: Props -> Props -> Props
unionProps ps qs = Props
  { pAdd = pAdd ps `union` pAdd qs
  , pMul = pMul ps `union` pMul qs
  , pExp = pExp ps `union` pExp qs
  , pLeq = pLeq ps `union` pLeq qs
  , pEq  = pEq  ps `union` pEq  qs
  }

getProp :: Props -> Maybe (Prop, Props)
getProp ps =
  case pAdd ps of { x:xs -> return (mk3 (EqFun Add) x, ps { pAdd = xs }); [] ->
  case pMul ps of { x:xs -> return (mk3 (EqFun Mul) x, ps { pMul = xs }); [] ->
  case pExp ps of { x:xs -> return (mk3 (EqFun Exp) x, ps { pExp = xs }); [] ->
  case pLeq ps of { x:xs -> return (mk2 Leq         x, ps { pLeq = xs }); [] ->
  case pEq  ps of { x:xs -> return (mk2 Eq          x, ps { pEq  = xs }); [] ->
  Nothing }}}}}
  where mk2 f (x,y)   = f x y
        mk3 f (x,y,z) = f x y z

elemProp :: Prop -> Props -> Bool
elemProp (EqFun op x y z) ps = elem (x,y,z) $ case op of
                                                Add -> pAdd ps
                                                Mul -> pMul ps
                                                Exp -> pExp ps
elemProp (Leq x y) ps  = elem (x,y) (pLeq ps)
elemProp (Eq x y) ps   = elem (x,y) (pEq ps)

isEmpty :: Props -> Bool
isEmpty ps = null (pAdd ps) && null (pMul ps) && null (pExp ps) &&
             null (pLeq ps) && null (pEq ps)

chooseProp :: Props -> [(Prop,Props)]
chooseProp ps =
  case getProp ps of
    Just (x,xs) -> (x,xs) : [ (y, addProp x ys) | (y,ys) <- chooseProp xs ]
    Nothing     -> []

propsList :: [Prop] -> Props
propsList = foldr addProp noProps

propsToList :: Props -> [Prop]
propsToList = unfoldr getProp




#include "TcTypeNatsRules.hs"




