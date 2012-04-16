> module Main(main) where

> import Text.PrettyPrint
> import Data.List(nub, (\\),sort,partition,mapAccumL)
> import Data.Char(toUpper)


> main :: IO ()
> main = print $ vcat $ map pp allRules
>   where allRules = funRules -- assocRules ++ concatMap specAx assocRules

> names :: [String]
> names = concatMap block [ 0 :: Integer .. ]
>   where block 0 = [ [c] | c <- [ 'a' .. 'z' ] ]
>         block n = [ c : show n | c <- [ 'a' .. 'z' ] ]


> specAx :: Rule -> [Rule]
> specAx r =
>   do (n, Prop op [ Var x, Var y, Var z ]) <- rAsmps r
>      let upd (Var a) | a `elem` [ x, y, z ] = Con a
>          upd a                              = a
>          updP (Prop o ts)                   = Prop o (map upd ts)
>      return Rule
>        { rForall = rForall r \\ [ x, y, z ]
>        , rAsmps  = [ (m,updP p) | (m,p) <- rAsmps r, m /= n ]
>        , rConc   = updP $ rConc r
>        , rSides  = nub $ Prop op [ Con x, Con y, Con z ] : rSides r
>        , rProof  = \ts ps -> rProof r (map conVar [x,y,z] ++ ts)
>                       ((n, DefAx op (Con x) (Con y)) : ps)
>        }
>   where conVar x                         = (x, Con x)




Terms, Propositions, and Rules
==============================

> data Term   = Con String        -- ^ Schematic number variable
>             | Num Integer       -- ^ A numeric constant
>             | Var String        -- ^ Uninterpreted constant
>               deriving (Eq,Ord)

> data Prop   = Prop { pOp :: Op, pTerms :: [Term] }
>               deriving Eq
>
> data Op     = Add | Mul | Exp | Eq | Leq
>               deriving (Eq,Ord,Show)
>
> data Proof  = By String [Term] [Proof]   -- Using an existing fact
>             | DefAx Op Term Term        -- Definitional axiom
>             | ByAsmp String

> data Rule   = Rule { rForall  :: [String]
>                    , rAsmps   :: [(String,Prop)]  -- named assumptions
>                    , rSides   :: [Prop]           -- no variables here
>                    , rConc    :: Prop
>                    , rProof   :: [(String,Term)]    -- inst. for terms
>                               -> [(String,Proof)]   -- inst. for asmps
>                               -> Proof
>                    }

> rule :: String -> [ Prop ] -> Prop -> Rule
> rule name asmps conc = Rule
>   { rForall = vars
>   , rAsmps  = named_asmps
>   , rSides  = []
>   , rConc   = conc
>   , rProof  = \ts ps -> By name (map (lkp "term"  ts) vars)
>                                 (map (lkp "proof" ps) (map fst named_asmps))
>   }
>   where vars = sort $ nub [ x | Prop _ ts <- conc : asmps, Var x <- ts ]
>         named_asmps  = zip pNames asmps
>         pNames       = [ toUpper a : as | a:as <- names ]
>         lkp msg xs x = case lookup x xs of
>                          Just a  -> a
>                          Nothing -> error ("Missing " ++ msg ++ ": " ++ x)



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


Generating Haskell
==================

> genSide :: Rule -> Prop -> Doc
> genSide r (Prop op [ a, b, c ])
>   | isGoal c = text "let" <+> pp c <+> text "=" <+>
>                pp a <+> text fOp <+> pp b
>   | isGoal a = text "Just" <+> pp a <+> text "<-" <+>
>                pp c <+> text lOp <+> pp b
>   | isGoal b = text "Just" <+> pp b <+> text "<-" <+>
>                pp c <+> text rOp <+> pp a
>   where
>   conc_vars         = pTerms (rConc r)
>   asmp_vars         = [ x | (_, Prop op1 ts) <- rAsmps r
>                           , not (op1 `elem` [ Eq, Leq ])
>                           , x <- ts
>                       ]
>   isGoal x          = x `elem` conc_vars &&
>                       all (`elem` asmp_vars) ([a,b,c] \\ [x])
>   (fOp,lOp,rOp) = case op of
>                     Add -> ("+", "`minus`",     "`minus`")
>                     Mul -> ("*", "`divide`",    "`divide`")
>                     Exp -> ("^", "`rootExact`", "`logExact`")
>                     _   -> error ("unexpected op(3): " ++ show op)
>
> genSide _ _ = error "unexpected side"

> termPatExpr :: Term -> Doc
> termPatExpr t@(Var _) = pp t
> termPatExpr t         = parens (text "Num" <+> pp t)



Example:

{a, b, c, d} (A : 1 <= a) (B : a * b == c) (C : a * d == c) =>
  DivFunL@(a, b, c, d)
    A
    B
    C
  : b == d

rule facts =
  do (proofB, a, b, c) <- lookupFact Mul facts
     proofA <- LEQ.prove facts 1 a
     (proofC, a1, d, c1) <- lookupFact Mul facts
     guard (a == a1)
     guard (c == c1)
     return (By DivFunL [a,b,c,d] proofA proofB proofC, Prop Eq [b,d])

> genRule :: Rule -> Doc
> genRule r =
>   let ((_,delayed,sides),d) = mapAccumL genAsmp ([],[], rSides r) (rAsmps r)
>   in text "do"
>        <+> (vcat d
>         $$ vcat (map (genSide r) sides)
>         $$ vcat (map genLeq delayed)
>         $$ text "return" <+> genTuple
>               [ genProof $
>                  rProof r [ (a,Var a) | a <- rForall r ]
>                           [ (a, ByAsmp (asmpName a)) | (a,_) <- rAsmps r ]
>               , genProp (rConc r)
>               ])
>
>   where
>   genAsmp (used,delayed,sides) (name, Prop Leq [a,b])
>     | all (`elem` used) (termVars a ++ termVars b) =
>                   ((used, delayed,            sides), genLeq (name,a,b))
>     | otherwise = ((used, (name,a,b):delayed, sides), empty)

>   genAsmp _ (_, Prop Eq _) = error "unexpected Eq in genAsmp"
>
>   genAsmp (used,delayed,sides) (name, prop) =
>     let ((used1,eqs),prop1) = renameProp (used,[]) prop
>         (here,later) = partition (itIsTime used1) sides
>     in ((used1,delayed,later), genOther name eqs prop1
>                                $$ vcat (map (genSide r) here))
>
>   genProp (Prop op ts) =
>     text "Prop" <+> text (show op) <+> genList (map pp ts)
>
>   genProof (By p ts as) = text "Using" <+> text p <+> genList (map pp ts)
>       $$ nest 2 (genList (map genProof as))
>   genProof (DefAx op a b) =
>     text "Using" <+> parens (text "Def" <> text (show op) <+> pp a <+> pp b)
>                                    <+> genList [] <+> genList []
>   genProof (ByAsmp t) = text t


>   termVars (Var x) = [x]
>   termVars _       = []
>
>   itIsTime vs (Prop _ ts) = null [ () | Con x <- ts, x `notElem` vs ]



>   genLeq (n,a,b) = text "Just" <+> text (asmpName n) <+> text "<-" <+>
>                     genList [ text "LEQ.prove facts" <+> pp a <+> pp b ]
>
>   genOther name eqs (Prop op [a,b,c]) =
>     genTuple [ text (asmpName name), pp a, pp b, pp c ]
>        <+> text "<-" <+> text "lookupProof facts" <+> text (show op)
>         $$ vcat (map genEq eqs)
>   genOther _ _ _ = error "Unexpected genOther"
>
>   genTuple ds  = parens (hsep (punctuate comma ds))
>   genList ds   = brackets (hsep (punctuate comma ds))
>
>   genEq (a,b)  = text "guard" <+> parens (text a <+> text "==" <+> text b)
>



>   renameProp used (Prop op ts) =
>     let (used1,ts1) = mapAccumL renameTerm used ts
>     in (used1, Prop op ts1)
>
>   renameTerm (used,eqs) (Var x)
>     | x `elem` used   = let y = newName names used
>                         in ( (y:used, (x,y):eqs), Var y )
>
>   renameTerm (used,eqs) (Con x)
>     | x `elem` used   = let y = newName (map (++"'") names) used
>                         in ( (y:used, (x,y):eqs), Con y )
>
>   renameTerm s t = (s, t)
>
>   newName ns used = head $ filter (`notElem` used) ns
>
>   asmpName n      = 'p' : n



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
>   pp (ByAsmp x)     = text x
>
>
> instance PP Rule where
>   pp r = tPars <+> pPars $$ nest 2 (pProof $$ pConc $$ pSides)
>     where
>     tPars = case rForall r of
>               [] -> empty
>               vs -> braces $ fsep $ punctuate comma $ map text vs
>     pPars = case rAsmps r of
>               [] -> empty
>               ts -> fsep [ parens (text x <+> colon <+> pp p) | (x,p) <- ts ]
>                     <+> text "=>"
>     pProof = pp $ rProof r [ (x,Var x) | x <- rForall r ]
>                            [ (x, ByAsmp x) | (x,_) <- rAsmps r ]
>     pConc  = colon <+> pp (rConc r)
>     pSides = case rSides r of
>                [] -> empty
>                ss -> text "if" <+> vcat (map pp ss)



