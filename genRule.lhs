> module Main(main) where

> import Text.PrettyPrint
> import Data.List(nub, (\\),sort,partition,mapAccumL,groupBy)
> import Data.Char(toUpper)
> import Data.Maybe(fromMaybe)
> import Control.Monad(guard,zipWithM)

> main :: IO ()
> main = print $ genRules allRules
>   where allRules = funRules ++ anihRules ++ otherRules ++ assocRules

> names :: [String]
> names = concatMap block [ 0 :: Integer .. ]
>   where block 0 = [ [c] | c <- [ 'a' .. 'z' ] ]
>         block n = [ c : show n | c <- [ 'a' .. 'z' ] ]





Terms, Propositions, and Rules
==============================

> data Term   = Con String        -- ^ Schematic number variable
>             | Num Integer       -- ^ A numeric constant
>             | Var String        -- ^ Uninterpreted constant
>               deriving (Eq,Ord,Show)

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

Instantiate Fun* with basic axioms:
  0 + a = a
  1 * a = a
  0 * a = 0


> funRules :: [Rule]
> funRules = baseFun ++ concatMap spec1 (frules ++ cancel)
>   where
>   frules =
>     [ rule "AddFun"  [ a :+ b === c, a :+ b === d ] (c === d)
>     , rule "MulFun"  [ a :* b === c, a :* b === d ] (c === d)
>     , rule "ExpFun"  [ a :^ b === c, a :^ b === d ] (c === d)
>     ]
>
>   cancel =
>     [ rule "SubFunR" [ a :+ b === c, d :+ b === c ] (a === d)
>     , rule "SubFunL" [ a :+ b === c, a :+ d === c ] (b === d)
>     , rule "DivFunR" [ Num 1 <== b, a :* b === c, d :* b === c ] (a === d)
>     , rule "DivFunL" [ Num 1 <== a, a :* b === c, a :* d === c ] (b === d)
>     , rule "SqrtFun" [ Num 1 <== b, a :^ b === c, d :^ b === c ] (a === d)
>     , rule "LogFun"  [ Num 2 <== a, a :^ b === c, a :^ d === c ] (b === d)
>     ]
>
>   a : b : c : d : _ = map Var names
>
>   spec1 r = r : take 1 (specAx r)
>
>   baseFun = do f <- frules
>                a <- baseRules
>                take 1 (cut f a)

> anihRules :: [Rule]
> anihRules =
>   [ rule "MulTo0L"  [ Num 2 <== a, a :* b === b ] (b === Num 0)
>   ]
>   where a : b : c : d : _ = map Var names


> otherRules :: [Rule]
> otherRules =
>   [ rule "AddComm"  [ a :+ b === c ] (b :+ a === c)
>   , rule "MulComm"  [ a :* b === c ] (b :* a === c)
>   ]
>
>   where a : b : c : d : _ = map Var names




> assocRules :: [Rule]
> assocRules = concatMap specAx $
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



Generating New Rules By Instantiation
=====================================


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




> baseRules :: [Rule]
> baseRules =
>   [ rule "Add0_R" []              (a :+ Num 0 === a)
>   , rule "Mul1_R" []              (a :* Num 1 === a)
>   , rule "Mul0_R" []              (a :* Num 0 === Num 0)
>   , rule "Exp0_R" []              (a :^ Num 0 === Num 1)
>   , rule "Exp1_R" []              (a :^ Num 1 === a)
>   , rule "Exp0_L" [ Num 1 <== a ] (Num 0 :^ a === Num 0)
>   , rule "Exp1_L" []              (Num 1 :^ a === Num 1)
>   ]
>   where a = Var "zz"


> -- assumng no name clashes
> cut frule arule =
>   do (n,a) <- rAsmps frule
>      Just su <- [ matchProp a (rConc arule) ]
>      return Rule { rForall = sort $ nub $ rForall arule ++
>                                      (rForall frule \\ map fst su)
>                  , rAsmps = rAsmps arule ++
>                               [ (m, instProp su p) | (m,p) <- rAsmps frule,
>                                                                     m /= n ]
>                  , rSides = rSides arule ++ rSides frule
>                  , rConc  = instProp su (rConc frule)
>                  , rProof = \ts ps ->
>                               rProof frule (su ++ ts)
>                                            ((n, rProof arule ts ps) : ps)
>                  }

> matchTerm :: Term -> Term -> Maybe [(String,Term)]
> matchTerm (Num x) (Num y) | x == y = Just []
> matchTerm (Var x) t                = Just [ (x,t) ]
> matchTerm _ _                      = Nothing -- assumes no 'Con's
>
> matchProp :: Prop -> Prop -> Maybe [(String,Term)]
> matchProp (Prop op1 ts1) (Prop op2 ts2)
>   = do guard (op1 == op2)
>        su  <- zipWithM matchTerm ts1 ts2
>        mapM check (groupBy (\(x,_) (y,_) -> x == y) (concat su))
>   where
>   check ~((x,y) : ys) = guard (all (== y) (map snd ys)) >> return (x,y)

> instTerm :: [(String,Term)] -> Term -> Term
> instTerm su t@(Var x) = fromMaybe t (lookup x su)
> instTerm _ t          = t
>
> instProp :: [(String,Term)] -> Prop -> Prop
> instProp su (Prop op ts) = Prop op (map (instTerm su) ts)






Generating Haskell
==================


Generate code for a side condition.
It uses the appropriate function or its inverse, depending
on where the free variables appear in the rule.  For example,

a' + b' = c'

  becomes: let c' = a' + b',            if c' appears only in the conclusion.
  becomes: Just a' <- [ c' `minus` a' ] if a' appears only in the conclusion.

> genSide :: Rule -> Prop -> Doc
> genSide r (Prop op [ a, b, c ])
>   | isGoal c = text "let" <+> pp c <+> text "=" <+>
>                pp a <+> text fOp <+> pp b
>   | isGoal a = text "Just" <+> pp a <+> text "<-" <+>
>                brackets (pp c <+> text lOp <+> pp b)
>   | isGoal b = text "Just" <+> pp b <+> text "<-" <+>
>                brackets (pp c <+> text rOp <+> pp a)
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
> genSide r p = error $ show (
>               text "unexpected side:" <+> pp p $$
>               text "rule:" $$ nest 2 (pp r)
>               )




Generate code for a rule.  A rule "fires" by emmiting its conclusion,
if it can find proofs about it hypothesis in the list of profvided facts.

Example:

{- {a, b, c, d} (A : 1 <= b) (B : a * b == c) (C : d * b == c) =>
     DivFunR@(a, b, c, d)
       A
       B
       C
     : a == d
-}
do (pB, a, b, c) <- lookupProof facts Mul
   Just pA <- [Leq.prove facts (Num 1) (b)]
   (pC, d, e, f) <- lookupProof facts Mul
   guard (c == f)
   guard (b == e)
   return Fact
     { factProp = Prop Eq [a, d]
     , factProof = Using DivFunR [a, b, c, d]
                     [pA, pB, pC]
     }


> genRule :: Rule -> Doc
> genRule r =
>   let leqs   = [ (n,a,b) | (n,Prop Leq [a,b]) <- rAsmps r ]
>       others = [ (n,p)   | (n,p@(Prop op _)) <- rAsmps r, op /= Leq ]
>       ((_,delayed,sides),d) = mapAccumL genAsmp ([],leqs,rSides r) others
>   in text "{-" <+> pp r $$
>      text "-}" $$
>      text "do"
>        <+> ( genEnabled
>         $$ vcat d
>         $$ vcat (map (genSide r) sides)
>         $$ vcat (map genLeq delayed)
>         $$ text "return" <+> text "Fact"
>         $$ nest 2
>            ( text "{ factProp" <+> text "=" <+> genProp (rConc r)
>           $$ text ", factProof" <+> text "=" <+>
>                genProof (rProof r [ (a,Var a) | a <- rForall r ]
>                           [ (a, ByAsmp (asmpName a)) | (a,_) <- rAsmps r ])
>           $$ text "}"
>          )
>         )
>   where
>   genEnabled =
>     let check op  = text "op" <+> text "==" <+> text (predName op)
>         genOr a b = a <+> text "||" <+> b
>     in text "guard" <+> parens (
>           foldr1 genOr $ map check $ nub [ p | (_,Prop p _) <- rAsmps r ])
>
>   genAsmp _ (_, Prop Leq _) = error "unexpected Leq in genAsmp"
>   genAsmp _ (_, Prop Eq _)  = error "unexpected Eq  in genAsmp"
>   genAsmp (used,leqs,sides) (name, prop) =
>     let ((used1,eqs),prop1) = renameProp (used,[]) prop
>         (hereS,laterS)      = partition (nowSide used1) sides
>         (hereL,laterL)      = partition (nowLeq used1) leqs
>     in ( (used1,laterL,laterS)
>        , genOther name eqs prop1
>            $$ vcat (map (genSide r) hereS)
>            $$ vcat (map genLeq      hereL)
>        )
>
>   allDefined ds vs       = all (`elem` ds) vs
>   nowLeq defined (_,a,b) = allDefined defined (concatMap varsOf [a,b])
>   nowSide defined s      = allDefined defined (varsOfProp s)

>   varsOfProp (Prop _ ts) = concatMap varsOf ts
>
>   varsOf (Var x) = [x]
>   varsOf (Con x) = [x]
>   varsOf (Num _) = []
>
>   genProp (Prop op ts) =
>     text "Prop" <+> text (predName op) <+> genList (map genTerm ts)
>
>   genProof (By p ts as) = text "Using" <+> text p <+> genList (map genTerm ts)
>       $$ nest 2 (genList (map genProof as))
>   genProof (DefAx op a b) =
>     text "Using" <+> parens (text "Def" <> text (predName op)
>                                         <+> genNumTerm a <+> genNumTerm b)
>                                    <+> genList [] <+> genList []
>   genProof (ByAsmp t) = text t


>   genLeq (n,a,b) = text "Just" <+> text (asmpName n) <+> text "<-" <+>
>        genList [ text "Leq.prove (getLeqFacts facts)" <+> parens (genTerm a)
>                                         <+> parens (genTerm b) ]
>
>   genOther name eqs (Prop op [a,b,c]) =
>     genTuple [ text (asmpName name), genTerm a, genTerm b, genTerm c ]
>        <+> text "<-" <+> text "lookupProof facts" <+> text (predName op)
>         $$ vcat (map genEq eqs)
>   genOther _ _ _ = error "Unexpected genOther"
>
>   genTerm (Var x) = text x
>   genTerm t       = text "Num" <+> genNumTerm t
>
>   genNumTerm (Num n)  = integer n
>   genNumTerm (Con n)  = text (conName n)
>   genNumTerm (Var _)  = error "Not a num term"
>
>   genTuple ds  = parens (hsep (punctuate comma ds))
>   genList ds   = brackets (hsep (punctuate comma ds))
>   genEq (a,b)  = text "guard" <+> parens (text a <+> text "==" <+> text b)
>

>   renameProp used (Prop op ts) =
>     let (used1,ts1) = mapAccumL renameTerm used ts
>     in (used1, Prop op ts1)
>
>   renameTerm (used,eqs) (Var x)
>     | x `elem` used   = let y = newName x used
>                         in ( (y:used, (x,y):eqs), Var y )
>     | otherwise       = ((x : used, eqs), Var x)
>
>   renameTerm (used,eqs) (Con x)
>     | conName x `elem` used   = let y = newName x used
>                                 in ( (y:used, (x,y):eqs), Con y )
>     | otherwise       = ((x : used, eqs) , Con x)
>
>   renameTerm s t = (s, t)

>   newName n used = head $ filter (`notElem` used)
>                           [ replicate p 'z' ++ "_" ++ n | p <- [ 1 .. ] ]
>   conName n       = n ++ "'"
>   asmpName n      = 'p' : n
>   predName n      = show n



> genRules :: [Rule] -> Doc
> genRules rs =
>   text "{-" <+> vcat
>     [ text "WARNING: This file is generated automatically."
>     , text "Plase do not modify, because changes may get lost."
>     ] $$
>   text "-}" $$
>   vcat (map text
>     [ "module TcTypeNatsRules(implied) where"
>     , "import TcTypeNatsBase"
>     , "import TcTypeNatsFacts"
>     , "import qualified TcTypeNatsLeq as Leq"
>     , "import TcTypeNatsProps"
>     , "import TcTypeNatsEval"
>     , "import Control.Monad(guard)"
>     , " "
>     , "lookupProof :: Facts -> Pred -> [(Proof, Term, Term, Term)]"
>     , "lookupProof fs p = [ (n, a, b, c)"
>     , "  | Fact { factProp = Prop _ [a,b,c], factProof = n }"
>     , "                                 <- getPropsFor p (getOtherFacts fs) ]"
>     , " "
>     , "implied :: Facts -> Pred -> [Fact]"
>     , "implied facts op = concat"
>     ]) $$ nest 2 (punct (map genRule rs) $$ text "]")
>
>   where punct []       = empty
>         punct (a : as) = text "[" <+> a $$ vcat [ text "," <+> b | b <- as ]









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
>   pp r = tPars <+> (pPars $$ pSides $$ line $$ pProof $$ pConc)
>     where
>     tPars = case rForall r of
>               [] -> empty
>               vs -> braces $ fsep $ punctuate comma $ map text vs
>     pPars = case rAsmps r of
>               [] -> empty
>               ts -> vcat [ text x <+> colon <+> pp p | (x,p) <- ts ]
>     pProof = pp $ rProof r [ (x,Var x) | x <- rForall r ]
>                            [ (x, ByAsmp x) | (x,_) <- rAsmps r ]
>     pConc  = colon <+> pp (rConc r)
>     pSides = case rSides r of
>                [] -> empty
>                ss -> text "if" <+> vcat (map pp ss)
>
>     line = text (replicate 20 '-')



