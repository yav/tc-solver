{-# LANGUAGE CPP #-}

module Test where

import Data.List(union,find)
import Control.Monad(mzero)
import qualified Data.Map as M

type Xi = String

data Term = Var Xi | Num Integer (Maybe Xi)
            deriving (Eq,Ord)

data Op   = Add | Mul | Exp | Leq | Eq deriving (Eq, Ord)
data Prop = Prop Op [Term]
            deriving Eq

instance Show Term where
  show (Var x)    = x
  show (Num x _)  = show x

instance Show Op where
  show Add = "+"
  show Mul = "*"
  show Exp = "^"
  show Leq = "<="
  show Eq  = "=="

instance Show Prop where

  show (Prop op [t1,t2,t3])
    | op == Add || op == Mul || op == Exp =
      show t1 ++ " " ++ show op ++ " " ++ show t2
                                ++ " == " ++ show t3
  show (Prop op [t1,t2])
    | op == Leq || op == Eq = show t1 ++ " " ++ show op ++ " " ++ show t2

  show (Prop op ts) = show op ++ " " ++ unwords (map show ts)

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

newtype Props = P (M.Map Op [[Term]])

noProps :: Props
noProps = P M.empty

addProp :: Prop -> Props -> Props
addProp (Prop op ts) (P props) = P (M.insertWith union op [ts] props)

filterProp :: (Prop -> Bool) -> Props -> Props
filterProp p (P ps) = P (M.mapMaybeWithKey upd ps)
  where upd op ts = case filter (p . Prop op) ts of
                      [] -> Nothing
                      xs -> Just xs

unionProps :: Props -> Props -> Props
unionProps (P as) (P bs) = P (M.unionWith union as bs)

getProp :: Props -> Maybe (Prop, Props)
getProp (P ps) =
  do ((op,t:ts),qs) <- M.minViewWithKey ps
     return (Prop op t, if null ts then P qs else P (M.insert op ts qs))

getPropsFor :: Op -> Props -> [[Term]]
getPropsFor op (P ps) = M.findWithDefault [] op ps

rmProps :: Op -> Props -> Props
rmProps op (P as) = P (M.delete op as)

elemProp :: Prop -> Props -> Bool
elemProp (Prop op ts) (P ps) = case M.lookup op ps of
                                 Nothing  -> False
                                 Just tss -> elem ts tss

isEmpty :: Props -> Bool
isEmpty (P ps) = M.null ps

propsList :: [Prop] -> Props
propsList = foldr addProp noProps

propsToList :: Props -> [Prop]
propsToList (P ps) = [ Prop op ts | (op,tss) <- M.toList ps, ts <- tss ]

chooseProp :: Props -> [(Prop,Props)]
chooseProp ps =
  case getProp ps of
    Nothing -> []
    Just (q,qs) -> (q,qs) : [ (a,addProp q as) | (a,as) <- chooseProp qs ]

type Var    = Xi
type Subst  = [ (Var,Term) ]

compose :: Subst -> Subst -> Subst
compose s2 s1 = [ (x, apSubst s2 t) | (x,t) <- s1 ] ++
                [ (x,t) | (x,t) <- s2, all (not . eqType x . fst) s1 ]

mgu :: Term -> Term -> Maybe Subst
mgu x y | x == y  = return []
mgu (Var x) t     = return [(x,t)] --- for simple terms no need to occur check
mgu t (Var x)     = return [(x,t)]
mgu _ _           = mzero

class ApSubst t where
  apSubst :: Subst -> t -> t

instance ApSubst t => ApSubst [t] where
  apSubst su ts = map (apSubst su) ts

instance ApSubst Term where
  apSubst su t@(Var x)  = case find (eqType x . fst) su of
                            Just (_,t1) -> t1
                            _ -> t
  apSubst _ t           = t

instance ApSubst Prop where
  apSubst su (Prop op ts) = Prop op (map (apSubst su) ts)

instance ApSubst Props where
  apSubst su (P ps) = P (M.map (apSubst su) ps)



#include "TcTypeNatsRules.hs"




