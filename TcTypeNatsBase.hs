{- Terms and Propositions -}
module TcTypeNatsBase
  ( Var(..)
  , Term(..)
  , num
  , Pred(..)
  , arity
  , Prop(..)
  , Goal(..)
  , Fact(..)
  , HasProp(..)
  , propPred
  , propArgs
  , Theorem(..)
  , Proof(..)
  , byRefl
  , isRefl
  , bySym
  , byTrans
  , byLeqDef
  , byLeqRefl
  , byLeqTrans
  , byLeqAsym
  , byLeq0
  , byMono
  , byCong
  , proofLet
  , PP(..)
  , TCN
  , EvVar
  , newEvVar
  ) where

import TcTypeNatsStandAlone
import Text.PrettyPrint
import Data.List(zipWith5)

newtype Var = V Xi

{- The ordering model (TcTypeNatsLeq) makes assumptions about the
   ordering on terms:
  - Variables should come before numbers.  This is useful because we can
    use "fst (split 0)" to get just the variable part of the map.
  - Number-terms should be ordered as their corresponding numbers.  This is
    useful so that we can use "splitLookup n" to find information about
    a number and its neighbours.
-}

data Term = Var Var | Num Integer

num :: Integer -> Term
num n = Num n


-- | Predicate symbols.  The ordering of these is important!
-- 'Eq' should come before 'Leq' which should come before all others.
-- This is used in module "TcTypeNatsProps" where function 'getOne'
-- will returns facts according to this order.  It is more efficient
-- to process equalities in this order (i.e., equalities first, then order,
-- and finaly everything else.)
data Pred = Eq | Leq | Add | Mul | Exp
            deriving (Show, Eq, Ord)


arity :: Pred -> Int
arity pr =
  case pr of
    Add -> 3
    Mul -> 3
    Exp -> 3
    Leq -> 2
    Eq  -> 2

-- | Propositions
data Prop = Prop Pred [Term]
            deriving (Eq,Ord)

_wfProp :: Prop -> Bool
_wfProp (Prop p xs) = arity p == length xs


-- | Goals represent propositions that need prood.
data Goal = Goal { goalName  :: EvVar, goalProp :: Prop }
            deriving (Eq,Ord)

-- | Facts represent propositions that have proof (including assumptions).
data Fact = Fact { factProof :: Proof, factProp :: Prop }



{-------------------------------------------------------------------------------
Convenient access to propositions embedded inside other types
-------------------------------------------------------------------------------}

class HasProp a where
  getProp :: a -> Prop

propPred :: HasProp a => a -> Pred
propPred p = case getProp p of
               Prop x _ -> x

propArgs :: HasProp a => a -> [Term]
propArgs p = case getProp p of
               Prop _ xs -> xs

instance HasProp Prop where getProp = id
instance HasProp Goal where getProp = goalProp
instance HasProp Fact where getProp = factProp

--------------------------------------------------------------------------------



{- Proofs and Theorems -}


data Theorem  = EqRefl      -- forall a.                        a = a
              | EqSym       -- forall a b.   (a = b)         => b = a
              | EqTrans     -- forall a b c. (a = b, b = c)  => a = c
              | Cong Pred   -- forall xs ys. (xs = ys, F xs) => F ys

              | LeqRefl     -- forall a.                         a <= a
              | LeqAsym     -- forall a b.   (a <= b, b <= a) => a = b
              | LeqTrans    -- forall a b c. (a <= b, b <= c) => a <= c
              | Leq0        -- forall a.                         0 <= a

              | DefAdd Integer Integer Integer
              | DefMul Integer Integer Integer
              | DefExp Integer Integer Integer
              | DefLeq Integer Integer

              -- Only for Add,Mul,and Exp
              | Mono Pred  -- forall as xs. (as <= xs) => F as <= F xs
                           {- forall a b c x y z. ( a <= x, b <= y
                                                  , a OP b = c, x OP y = z
                                                  ) => c <= z -}

              | AddLeq
              | MulLeq
              | ExpLeq1
              | ExpLeq2
              | Add0 | Mul0 | Mul1 | Root0 | Root1 | Log1
              | AddComm | MulComm
              | SubL | SubR | DivL | DivR | Root | Log
              | MulGrowL | MulGrowR | ExpGrow
              | AddAssoc | MulAssoc | AddMul | MulExp | ExpAdd | ExpMul
              | AddAssocSym | MulAssocSym | AddMulSym
              | MulExpSym | ExpAddSym | ExpMulSym
              | FunAdd | FunMul | FunExp
                deriving Show


data Proof    = ByAsmp EvVar
              | Using Theorem [Term] [Proof]   -- Instantiation, sub-proofs

byRefl :: Term -> Proof
byRefl t = Using EqRefl [t] []

isRefl :: Proof -> Bool
isRefl (Using EqRefl _ _) = True
isRefl _ = False

bySym :: Term -> Term -> Proof -> Proof
bySym _ _ p@(Using EqRefl _ _) = p
bySym _ _ (Using EqSym _ [p]) = p
bySym t1 t2 p = Using EqSym [t1,t2] [p]

byTrans :: Term -> Term -> Term -> Proof -> Proof -> Proof
-- byTrans t1 t2 _ p1 p2 = byCong Eq [ bySym t1 t2 p1, p2 ] (byRefl t2)
-- (r = s, s = t) => r = t
-- cong = (s = r, s = t, s = s
byTrans _ _ _ (Using EqRefl _ _) p = p
byTrans _ _ _ p (Using EqRefl _ _) = p
byTrans t1 t2 t3 p1 p2 = Using EqTrans [t1,t2,t3] [p1,p2]


byLeqDef :: Integer -> Integer -> Proof
byLeqDef x y = Using (DefLeq x y) [] []

byLeqRefl :: Term -> Proof
byLeqRefl t = Using LeqRefl [t] []

byLeqTrans :: Term -> Term -> Term -> Proof -> Proof -> Proof
byLeqTrans _ _ _ (Using LeqRefl _ _) p = p
byLeqTrans _ _ _ p (Using LeqRefl _ _) = p
byLeqTrans t1 t2 t3 p1 p2 = Using LeqTrans [t1,t2,t3] [p1,p2]

byLeqAsym :: Term -> Term -> Proof -> Proof -> Proof
byLeqAsym t1 t2 p1 p2 = Using LeqAsym [t1,t2] [p1,p2]

byLeq0 :: Term -> Proof
byLeq0 t = Using Leq0 [t] []

byMono :: Pred -> [Term] -> [Proof] -> Proof
byMono p ts@[_,_,_,_,_,_] ps@[_,_,_,_]
  | p `elem` [Add,Mul,Exp]  = Using (Mono p) ts ps
byMono _ _ _ = error "byMono: Incorrect argumnets"


-- (x1 = y1, x2 = y2, P x1 x2) => P y1 y2
byCong :: Pred -> [Term] -> [Proof] -> Proof -> Proof
byCong _ _ qs q | all isRefl qs = q

-- (x1 == y1, x2 == y2, x1 == x2) => y1 = y2
byCong Eq [x1,x2,y1,y2] [ xy1, xy2 ] xx =
                  byTrans y1 x2 y2 (byTrans y1 x1 x2 (bySym x1 y1 xy1) xx) xy2
-- (p1: x1 = y1, p2: x2 = y2,
--     byCong (q1 : a1 = x1) (q2 : a2 = x2) (q : F z1 z2) : F y1 y2)
-- => byCong F (as ++ ys) (trans q1 p1, trans q2 p2) q
byCong p ts ps (Using (Cong _) us qs0) =
  let qs = init qs0
      q  = last qs0

      as      = take (arity p) us
      (xs,ys) = splitAt (arity p) ts

  in byCong p (as ++ ys) (zipWith5 byTrans as xs ys qs ps) q

byCong p ts qs q = Using (Cong p) ts (qs ++ [q])


proofLet :: EvVar -> Proof -> Proof -> Proof
proofLet x p1 (ByAsmp y) | x == y     = p1
                         | otherwise  = ByAsmp y
proofLet x p1 (Using EqTrans [t1,t2,t3] [s1,s2]) =
  byTrans t1 t2 t3 (proofLet x p1 s1) (proofLet x p1 s2)
proofLet x p1 (Using EqSym [t1,t2] [s1]) =
  bySym t1 t2 (proofLet x p1 s1)
proofLet x p1 (Using (Cong p) ts ss) = byCong p ts (init ss1) (last ss1)
  where ss1 = map (proofLet x p1) ss
proofLet x p1 (Using t ts ps) = Using t ts (map (proofLet x p1) ps)

--------------------------------------------------------------------------------









-- Comparisons -----------------------------------------------------------------

instance Eq Var where
  V x == V y  = eqType x y

instance Ord Var where
  compare (V x) (V y) = cmpType x y

instance Eq Term where
  Var x == Var y = x == y
  Num x == Num y = x == y
  _     == _     = False

instance Ord Term where
  compare (Var x) (Var y) = compare x y
  compare (Var _) _       = LT
  compare _ (Var _)       = GT
  compare (Num x) (Num y) = compare x y

{- We compare facts based only on the property they state because we are
not interested in facts that state the same thing but differ in the proof. -}

instance Eq Fact where
  x == y = factProp x == factProp y

instance Ord Fact where
  compare x y = compare (factProp x) (factProp y)




-- Pretty Printing -------------------------------------------------------------

class PP a where
  pp :: a -> Doc

instance PP Var where
  pp (V x) = pprXi x

instance PP Term where
  pp (Var x)  = pp x
  pp (Num x)  = integer x

instance PP Pred where
  pp op =
    case op of
      Add -> text "+"
      Mul -> text "*"
      Exp -> text "^"
      Leq -> text "<="
      Eq  -> text "=="

instance PP Prop where

  pp (Prop op [t1,t2,t3])
    | op == Add || op == Mul || op == Exp =
      pp t1 <+> pp op <+> pp t2 <+> text "==" <+> pp t3

  pp (Prop op [t1,t2])
    | op == Leq || op == Eq = pp t1 <+> pp op <+> pp t2

  pp (Prop op ts) = pp op <+> fsep (map pp ts)

instance PP Fact where
  pp f = text "G:" <+> pp (factProp f)

instance PP Goal where
  pp f = text "W:" <+> pp (goalProp f)

instance PP Proof where
  pp (ByAsmp e) = pprEvVar e
  pp (Using x ts ps) = text (show x) <> inst $$ nest 2 (vcat (map pp ps))
    where inst = case ts of
                   [] -> empty
                   _  -> text "@" <> parens (fsep $ punctuate comma $ map pp ts)





