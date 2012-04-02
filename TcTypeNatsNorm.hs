module TcTypeNatsNorm where

import TcTypeNatsBase
import Data.Maybe(mapMaybe)
import Control.Monad(guard, msum)

-- All variables are distinct
data NormProp = AddK Integer Var Var
              | AddB Var Var Integer
              | Add3 Var Var Var
              | MulK Integer Var Var
                deriving Eq

data Res      = Ok NormProp
              | Improved [ Prop ]
              | Impossible
              | Unknown


(===) :: Term -> Term -> Prop
x === y = Prop Eq [ x, y ]

normAdd :: Term -> Term -> Term -> Res

normAdd (Num 0 _) y z             = Improved [ y === z ]
normAdd x y (Num 0 _)             = Improved [ x === num 0, y === num 0 ]

normAdd x y z
  | x == z                        = Improved [ y === num 0 ]
  | y == z                        = Improved [ x === num 0 ]
  | x == y                        = Improved [ Prop Mul [ num 2, x, z ] ]

normAdd (Var x) (Var y) (Var z)   = Ok (Add3 x y z)
normAdd (Num x _) (Var y) (Var z) = Ok (AddK x y z)
normAdd (Var x) (Var y) (Num z _) = Ok (AddB x y z)

normAdd (Num x _) (Num y _) z     = Improved [ z === num (x + y) ]

normAdd (Num x _) y (Num z _)     = if x <= z
                                      then Improved [ y === num (z - x) ]
                                      else Impossible

normAdd x@(Var {}) y@(Num {}) z   = normAdd y x z



normMul :: Term -> Term -> Term -> Res
normMul (Num 0 _) _ z             = Improved [ z === num 0 ]
normMul (Num 1 _) y z             = Improved [ y === z ]
normMul x y (Num 1 _)             = Improved [ x === num 1, y === num 1 ]

normMul (Num x _) (Var y) (Var z)
  | y == z                        = Improved [ Var y === num 0 ]
  | otherwise                     = Ok (MulK x y z)

normMul (Num x _) (Num y _) z     = Improved [ z === num (x * y) ]

normMul (Num x _) y (Num z _)     = case divMod z x of
                                      (a, 0) -> Improved [ y === num a ]
                                      _      -> Impossible

normMul x@(Var {}) y@(Num {}) z   = normMul y x z

normMul _ _ _                     = Unknown






findSum :: [NormProp] -> Var -> Var -> [Term]
findSum ps a b = mapMaybe check ps
  where
  check (Add3 a' b' c) | a == a' && b == b' = Just (Var c)
  check (AddB a' b' c) | a == a' && b == b' = Just (num c)
  check _                                   = Nothing

findSumK :: [NormProp] -> Integer -> Var -> [Var]
findSumK ps a b = [ c | AddK a' b' c <- ps, a == a', b == b' ]

addsTo :: [NormProp] -> Term -> [(Term,Term)]
addsTo ps (Num z _) = [ (Var x, Var y) | AddB x y z' <- ps, z == z' ]
addsTo ps (Var z)   = mapMaybe check ps
  where
  check (Add3 x y z') | z == z' = Just (Var x, Var y)
  check (AddK x y z') | z == z' = Just (num x, Var y)
  check _                       = Nothing


findMulK :: [NormProp] -> (Integer -> Bool) -> (Var -> Bool) -> (Var -> Bool) ->
                                                        [(Integer,Var,Var)]
findMulK ps pk pa pb = [ (k,a,b) | MulK k a b <- ps, pk k, pa a, pb b ]

pAny :: a -> Bool
pAny _ = True


distrib :: [NormProp] -> NormProp -> [Prop]
distrib ps (MulK k a x) =

     -- (=>) k * a1 + k * a2 = k * (a1 + a2)
  do (_,b,y) <- findMulK ps (k ==) pAny pAny
     c <- findSum ps a b
     z <- findSum ps x y
     return (Prop Mul [num k, c, z])

  ++ -- (<=) k * a1 + k * a2 = k * (a1 + a2)
  do (_, a1, s1) <- findMulK ps (k ==) pAny pAny
     let addsToA a2 = a `elem` [ s | Var s <- findSum ps a1 a2 ]
     (_,_,s2) <- findMulK ps (k ==) addsToA pAny
     return (Prop Add [ Var s1, Var s2, Var x ])

  ++ -- (=>) k * a + k' * a = (k + k') * a
  do (k',_,y) <- findMulK ps pAny (a ==) pAny
     z        <- findSum ps x y
     return (Prop Mul [ num (k + k'), Var a, z ])

  ++ -- (<=) k1 * a + k2 * a = (k1 + k2) * a
  do (k1,_,s1) <- findMulK ps (<  k + 1)  (a ==) pAny
     (_ ,_,s2) <- findMulK ps (== k - k1) (a ==) pAny
     return (Prop Add [ Var s1, Var s2, Var x ])

distrib ps (Add3 x y z) =

     -- LHS: k * a + k * b = k * (a + b)
  do (k,a,_) <- findMulK ps pAny   pAny (x ==)
     (_,b,_) <- findMulK ps (k ==) pAny (y ==)
     ab      <- findSum ps a b
     return (Prop Mul [ num k, ab, Var z ])

  ++ -- RHS: k * a + k * b = k * (a + b)
  do (k, _, res) <- findMulK ps pAny   (z ==) pAny
     (_, _, s1)  <- findMulK ps (k ==) (x ==) pAny
     (_, _, s2)  <- findMulK ps (k ==) (y ==) pAny
     return (Prop Add [ Var s1, Var s2, Var res ])

distrib ps (AddK x y z) =

     -- LHS: k * a + k * b = k * (a + b)
  do (k,b,_) <- findMulK ps pAny pAny (y ==)
     ab <- case divMod x k of
             (a,0) -> findSumK ps a b
             _     -> []
     return (Prop Mul [ num k, Var ab, Var z ])

  ++ -- RHS: k * a + k * b = k * (a + b)
  do (k, _, res) <- findMulK ps pAny   (z ==) pAny
     (_, _, s2)  <- findMulK ps (k ==) (y ==) pAny
     return (Prop Add [ num (k * x), Var s2, Var res ])

distrib ps (AddB x y z) =

     -- LHS: k * a + k * b = k * (a + b)
  do (k,a,_) <- findMulK ps pAny   pAny (x ==)
     (_,b,_) <- findMulK ps (k ==) pAny (y ==)
     ab      <- findSum ps a b
     return (Prop Mul [ num k, ab, num z ])

  ++ -- RHS: k * a + k * b = k * (a + b)
  do (k, _, s1) <- findMulK ps pAny   (x ==) pAny
     (_, _, s2) <- findMulK ps (k ==) (y ==) pAny
     return (Prop Add [ Var s1, Var s2, num (k * z) ])



fun :: [NormProp] -> NormProp -> [Prop]
fun ps (MulK k a b) =
  do (_, _, b') <- findMulK ps (k ==) (a ==) pAny
     return (Prop Eq [ Var b, Var b' ])

fun ps (Add3 x y z) =
  do z' <- findSum ps x y
     return (Prop Eq [ Var z, z' ])

fun ps (AddK x y z) =
  do z' <- findSumK ps x y
     return (Prop Eq [ Var z, Var z' ])

fun ps (AddB x y z) =
  do z' <- findSum ps x y
     return (Prop Eq [ num z, z' ])



cancel :: [NormProp] -> NormProp -> [Prop]
cancel ps (MulK k a b) =
  do (_,a',_) <- findMulK ps (k ==) pAny (b ==)
     return (Prop Eq [ Var a, Var a' ])
     -- XXX: by using the leq model, we could do the other cancellation
     -- law too: if we knew that 1 <= a, then we could check that if
     -- we have another "k1 * a = b", "k1 = k2".  This would detect
     -- inconcistencies, but it does not add new information about
     -- the variables.

cancel ps (Add3 x y z) =
  do (x',y') <- addsTo ps (Var z)
     msum [ guard (Var x == x') >> return (Prop Eq [ Var y, y' ])
          , guard (Var y == y') >> return (Prop Eq [ Var x, x' ])
          ]

cancel ps (AddK x y z) =
  do (x',y') <- addsTo ps (Var z)
     msum [ guard (num x == x') >> return (Prop Eq [ Var y, y' ])
          , guard (Var y == y') >> return (Prop Eq [ num x, x' ])
          ]

cancel ps (AddB x y z) =
  do (x',y') <- addsTo ps (num z)
     msum [ guard (Var x == x') >> return (Prop Eq [ Var y, y' ])
          , guard (Var y == y') >> return (Prop Eq [ Var x, x' ])
          ]

-- XXX: Need a better way to deal with associativity:
-- There is a mirrored set of equations for (non-linear) multiplication

-- (a + b) + c = a + (b + c)
assoc :: [NormProp] -> NormProp -> [Prop]
assoc ps (Add3 x y z) =
  -- LL
  do (ss2,tot) <- mapMaybe checkLL ps
     s2 <- ss2
     return (Prop Add [Var x, s2, tot])

  ++ -- LR
  do (a,b) <- addsTo ps (Var x)
     s2    <- case b of
                Var b'   -> findSum  ps b' y
                Num b' _ -> map Var (findSumK ps b' y)
     return (Prop Add [a,s2,Var z])

  ++ -- RL
  do (b,c) <- addsTo ps (Var y)
     s1    <- case b of
                Var b'  -> findSum ps x b'
                Num {}  -> []
     return (Prop Add [s1, c, Var z])

  ++ -- RR
  do (ss1,tot) <- mapMaybe checkRR ps
     s1 <- ss1
     return (Prop Add [s1, Var y, tot])

  where
  checkLL (Add3 xy c d) | xy == z = Just (findSum ps y c, Var d)
  checkLL (AddB xy c d) | xy == z = Just (findSum ps y c, num d)
  checkLL _                       = Nothing

  checkRR (Add3 a xy d) | xy == z = Just (findSum ps a x,            Var d)
  checkRR (AddK a xy d) | xy == z = Just (map Var (findSumK ps a x), Var d)
  checkRR (AddB a xy d) | xy == z = Just (findSum ps a x,            num d)
  checkRR _                       = Nothing

-- (a + b) + c = a + (b + c)
assoc ps (AddK x y z) =
  -- LL
  do (ss2,tot) <- mapMaybe checkLL ps
     s2 <- ss2
     return (Prop Add [num x, s2, tot])

  ++ -- LR
  do AddB a b ab <- ps
     guard (ab == x)
     s2 <- findSum ps b y
     return (Prop Add [Var a,s2,Var z])

  ++ -- LR (axiom)
  do AddK b y' s2 <- ps
     guard (y == y' && b <= x)
     let a = x - b
     return (Prop Add [ num a, Var s2, Var z ])

  ++ -- RL
  do (b,c) <- addsTo ps (Var y)
     s1    <- case b of
                Var b'   -> map Var (findSumK ps x b')
                Num b' _ -> return (num (x + b'))
     return (Prop Add [s1, c, Var z])

  ++ -- RR
  do AddK a xy d <- ps
     guard (xy == z)
     return (Prop Add [num (a + x), Var y, Var d])

  where
  checkLL (Add3 xy c d) | xy == z = Just (findSum ps y c, Var d)
  checkLL (AddB xy c d) | xy == z = Just (findSum ps y c, num d)
  checkLL _                       = Nothing


-- (a + b) + c = a + (b + c)
assoc ps (AddB x y z) =
  -- LL
  do AddK xy c d <- ps
     guard (xy == z)
     s2 <- findSum ps y c
     return (Prop Add [Var x, s2, Var d])

  ++ -- LR
  do (a,b) <- addsTo ps (Var x)
     s2    <- case b of
                Var b'   -> findSum  ps b' y
                Num b' _ -> map Var (findSumK ps b' y)
     return (Prop Add [a,s2,num z])

  ++ -- RL
  do (b,c) <- addsTo ps (Var y)
     s1    <- case b of
                Var b'  -> findSum ps x b'
                Num {}  -> []
     return (Prop Add [s1, c, num z])

assoc _ (MulK _ _ _) = []



commute :: NormProp -> [Prop]
commute (Add3 x y z) = [ Prop Add [ Var y, Var x, Var z ] ]
commute (AddB x y z) = [ Prop Add [ Var y, Var x, num z ] ]
commute _            = []


extend :: [NormProp] -> NormProp -> [Prop]
extend ps p = commute p ++ fun ps p ++ cancel ps p ++ assoc ps p ++ distrib ps p



fromProp :: Prop -> Res
fromProp (Prop Add [ x, y, z ]) = normAdd x y z
fromProp (Prop Mul [ x, y, z ]) = normMul x y z
fromProp _                      = Unknown


toProp :: NormProp -> Prop
toProp (Add3 x y z) = Prop Add [ Var x, Var y, Var z ]
toProp (AddK x y z) = Prop Add [ num x, Var y, Var z ]
toProp (AddB x y z) = Prop Add [ Var x, Var y, num z ]
toProp (MulK x y z) = Prop Mul [ num x, Var y, Var z ]






