> module Main(main) where

> import Text.PrettyPrint
> import Data.List(nub, (\\),partition)
> import Control.Monad(guard)
> import Data.Char(toUpper)



Terms and Propositions
======================

> data Term   = Con String        -- ^ Schematic number variable
>             | Num Integer       -- ^ A numeric constant
>             | Var String        -- ^ Uninterpreted constant
>               deriving (Eq,Ord)

> data Prop   = Prop { pPred :: Op, pArgs :: [Term] }
>               deriving Eq
>
> data Op     = Add | Mul | Exp | Eq | Leq
>               deriving (Eq,Ord,Show)
>
> arity :: Op -> Int
> arity op | op `elem` [Add,Mul,Exp]  = 3
>          | op `elem` [Eq,Leq]       = 2
>          | otherwise                = error "bug: arity, unknown op"

> data Proof  = By String [Term] [Proof]   -- Using an existing fact
>             | DefAx Op Term Term        -- Definitional axiom




> main = undefined


Rules
=====



> data Rule   = Rule { rVars  :: [String] -- all uninterpreted constants
>                    , rAsmps :: [(String,Prop)]
>                    , rSides :: [Prop]   -- no uninterpted constants here
>                    , rConc  :: Prop
>                    , rProof :: [(String,Term)]
>                             -> [(String,Proof)]
>                             -> Proof
>                    }

> rule :: String -> [ Prop ] -> Prop -> Rule
> rule name asmps conc = Rule
>   { rVars   = vars
>   , rAsmps  = named_asmps
>   , rSides  = []
>   , rConc   = conc
>   , rProof  = \ts ps -> By name (map (lkp "term" ts) vars)
>                                 (map (lkp "proof" ps) (map fst named_asmps))
>   }
>   where vars         = nub [ x | Prop _ ts <- conc : asmps, Var x <- ts ]
>         named_asmps  = zip pNames asmps
>         pNames       = [ toUpper a : as | a:as <- names ]
>         lkp msg xs x = case lookup x xs of
>                          Just a  -> a
>                          Nothing -> error ("Missing " ++ msg ++ ": " ++ x)

> specAx :: Op -> Rule -> [Rule]
> specAx op r =
>   do (n, Prop op' [ Var x, Var y, Var z ]) <- rAsmps r
>      guard (op == op')
>      let upd (Var a) | a `elem` [ x, y, z ] = Con a
>          upd a                              = a
>          updP (Prop o ts)                   = Prop o (map upd ts)
>          (ss,as) = partition isSide [ (m,updP p) | (m,p) <- rAsmps r, m /= n ]
>      return Rule
>        { rVars   = rVars r \\ [ x, y, z ]
>        , rAsmps  = as
>        , rConc   = updP $ rConc r
>        , rSides  = nub $ Prop op' [ Con x, Con y, Con z ]
>                        : map snd ss ++ rSides r
>        , rProof  = \ts ps -> rProof r (map conVar [x,y,z] ++ ts)
>                       ((n, DefAx op (Con x) (Con y)) : map sideProof ss ++ ps)
>        }
>   where conVar x = (x, Con x)
>         isSide (_,Prop _ ts) = null [ () | Var _ <- ts ]
>         sideProof (m, Prop op (t1:t2:_)) = (m, DefAx op t1 t2)




Pretty Printing
===============

> class PP a where
>   pp :: a -> Doc
>
>
> instance PP Term where
>   pp (Con c)  = text c <> text "'"
>   pp (Num n)  = integer n
>   pp (Var x)  = text x
>
>
> instance PP Op where
>   pp op = text $ case op of
>                    Add  -> "+"
>                    Mul  -> "*"
>                    Exp  -> "^"
>                    Eq   -> "=="
>                    Leq  -> "<="
>
>
> instance PP Prop where
>   pp (Prop op [ t1, t2 ])     = pp t1 <+> pp op <+> pp t2
>   pp (Prop op [ t1, t2, t3 ]) = pp t1 <+> pp op <+> pp t2
>                                                 <+> text "==" <+> pp t3
>
>   pp (Prop op _)   = error ("unexpected op: " ++ show op)
>
> instance PP Proof where
>   pp (By x ts ps) = text x <> ppTs $$ nest 2 ppPs
>     where
>     ppTs | null ts = empty
>          | True    = char '@' <> parens (fsep $ punctuate comma $ map pp ts)
>     ppPs = vcat $ map pp ps
>   pp (DefAx op x y) = text "Def" <> text (show op) <+> pp x <+> pp y
>
>
> instance PP Rule where
>   pp r = tPars <+> pPars $$ nest 2 (pProof $$ pConc $$ pSides)
>     where
>     tPars = case rVars r of
>               [] -> empty
>               vs -> braces $ fsep $ punctuate comma $ map text vs
>     pPars = case rAsmps r of
>               [] -> empty
>               ts -> fsep [ parens (text x <+> colon <+> pp p) | (x,p) <- ts ]
>                     <+> text "=>"
>     pProof = pp $ rProof r [ (x,Var x) | x <- rVars r ]
>                            [ (x, By x [] []) | (x,_) <- rAsmps r ]
>     pConc  = colon <+> pp (rConc r)
>     pSides = case rSides r of
>                [] -> empty
>                ss -> text "if" <+> vcat (map pp ss)

> names :: [String]
> names = concatMap block [ 0 :: Integer .. ]
>   where block 0 = [ [c] | c <- [ 'a' .. 'z' ] ]
>         block n = [ c : show n | c <- [ 'a' .. 'z' ] ]


Syntactic Sugar
===============

> data LHS = Term :+ Term | Term :* Term | Term :^ Term

> class EqSugar t where
>   (===) :: t -> Term -> Prop

> instance EqSugar LHS where
>   t1 :+ t2 === t3 = Prop Add [ t1, t2, t3 ]
>   t1 :* t2 === t3 = Prop Mul [ t1, t2, t3 ]
>   t1 :^ t2 === t3 = Prop Exp [ t1, t2, t3 ]
>
> instance EqSugar Term where
>    t1 === t2      = Prop Eq [ t1, t2 ]
>
> (<==) :: Term -> Term -> Prop
> t1 <== t2 = Prop Leq [ t1, t2 ]





Concrete Rules
==============

> funRules :: [Rule]
> funRules =
>   [ rule "AddFun"  [ a :+ b === c, a :+ b === d ] (c === d)
>   , rule "SubFunR" [ a :+ b === c, d :+ b === c ] (a === d)
>   , rule "SubFunL" [ a :+ b === c, a :+ d === c ] (b === d)
>   ]
>   ++
>   [ rule "MulFun"  [              a :* b === c, a :* b === d ] (c === d)
>   , rule "DivFunR" [ Num 1 <== b, a :* b === c, d :* b === c ] (a === d)
>   , rule "DivFunL" [ Num 1 <== a, a :* b === c, a :* d === c ] (b === d)
>   ]
>   ++
>   [ rule "ExpFun"  [              a :^ b === c, a :^ b === d ] (c === d)
>   , rule "SqrtFun" [ Num 1 <== b, a :^ b === c, d :^ b === c ] (a === d)
>   , rule "LogFun"  [ Num 2 <== a, a :^ b === c, a :^ d === c ] (b === d)
>   ]
>
>   where a : b : c : d : _ = map Var names


> assocRules :: [Rule]
> assocRules =
>   [ rule "AddAssocFL"
>       [ a :+ b === x, b :+ c === y, a :+ y === z ]
>       (x :+ c === z)
>
>   , rule "AddAssocFR"
>       [ a :+ b === x, b :+ c === y, x :+ c === z ]
>       (a :+ y === z)
>
>   , rule "AddAssocBL"
>       [ b :+ c === y, a :+ y === z, x :+ c === z ]
>       (a :+ b === x)
>
>   , rule "AddAssocBR"
>       [ a :+ b === x, x :+ c === z, a :+ y === z ]
>       (b :+ c === y)
>   ]
>   ++
>   [ rule "MulAssocFL"
>     [ a :* b === x, b :* c === y, a :* y === z ]
>     (x :* c === z)
>
>   , rule "MulAssocFR"
>       [ a :* b === x, b :* c === y, x :* c === z ]
>       (a :* y === z)
>
>   , rule "MulAssocBL"
>       [ Num 1 <== c, b :* c === y, a :* y === z, x :* c === z ]
>       (a :* b === x)
>
>   , rule "MulAssocBR"
>       [ Num 1 <== a, a :* b === x, x :* c === z, a :* y === z ]
>       (b :* c === y)
>   ]
>
>   where a : b : c : x : y : z : _ = map Var names

>
> example = assocRules ++ [ r1 | r <- assocRules , op <- [Add,Mul]
>                         , r1 <- specAx op r ]



