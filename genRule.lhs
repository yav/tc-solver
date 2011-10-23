> module Main(main) where

> import qualified Data.Map as M
> import Text.PrettyPrint
> import Data.List
> import Data.Ord(comparing)
> import Data.Maybe(maybeToList,listToMaybe,mapMaybe)
> import Debug.Trace
> import Control.Monad(when,guard,MonadPlus(..),unless,ap,liftM)



Terms and Propositions

> data Var    = V String
>             | NV String
>               deriving (Eq,Ord)
>
> numV :: Var -> Bool
> numV (NV _) = True
> numV (V _)  = False

> data Term   = App Op Term Term
>             | Const Integer
>             | Var Var
>               deriving (Eq,Ord)
>
> data Prop   = Prop { pPred :: Op, pArgs :: [Term] }
>               deriving Eq
>
> data Op     = Add | Mul | Exp | Eq | Leq
>               deriving (Eq,Ord)
>
> arity :: Op -> Int
> arity op | op `elem` [Add,Mul,Exp]  = 3
>          | op `elem` [Eq,Leq]       = 2
>          | otherwise                = error "bug: arity, unknown op"

Utilities for easy input

> instance Num Term where
>   fromInteger = Const
>   x + y       = App Add x y
>   x * y       = App Mul x y
>   abs         = error "Term: abs"
>   signum      = error "Term: signum"
>
> infixr 8 ^^^
> (^^^) :: Term -> Term -> Term
> x ^^^ y = App Exp x y
>
> infix 2 ===
> (===) :: Term -> Term -> Prop
> x === y = Prop Eq [x,y]
>
> infix 2 <==
> (<==) :: Term -> Term -> Prop
> t1 <== t2 = Prop Leq [t1,t2]

> data RuleHL = RuleHL String [Prop] Prop

> aRule :: String -> [Prop] -> Prop -> RuleHL
> aRule = RuleHL
>
> rule :: String -> Prop -> RuleHL
> rule name r = aRule name [] r


Rules

> data Rule   = Rule { rAsmps :: [Prop]
>                    , rSides :: [Prop]      -- only NV vars here
>                    , rConc  :: Prop
>                    , rProof :: Proof
>                    }
>
> isSide :: Prop -> Bool
> isSide  = all numV . fvs
>
> mkRule :: String -> [Prop] -> Prop -> Rule
> mkRule name as r = ru
>   where
>   ru = Rule
>     { rAsmps  = asmps
>     , rSides  = nub ((if isAx then [r] else []) ++ sides)
>     , rConc   = r
>     , rProof  = By thm vars [ ByAsmp n | (n,_) <- zip [0..] asmps ]
>     }
>   isAx            = isSide r
>   (sides,asmps')  = partition isSide as
>   asmps           = nub asmps'
>   vars            = map Var $ nub $ filter (not . numV) $ fvs (asmps,r)
>   thm             = Thm name (if isAx then pArgs r else [])


Keeping Track of Proofs

> data Theorem  = Thm String [Term]
>
> data Proof    = By Theorem [Term] [Proof]   -- Using an existing fact
>               | ByAsmp !Int                 -- Using an assumption
>
> instance FVS Proof where
>   fvs p = case p of
>             By x ts ps -> fvs (x, (ts,ps))
>             ByAsmp _   -> []
>
>   apSubst su p =
>     case p of
>       By x ts ps -> By (apSubst su x) (apSubst su ts) (apSubst su ps)
>       ByAsmp n   -> ByAsmp n
>
> instance FVS Theorem where
>   fvs (Thm _ ts) = fvs ts
>   apSubst su (Thm a ts) = Thm a (apSubst su ts)
>
> -- Used when new proof arguments come in scope.
> liftAsmps :: Int -> Proof -> Proof
> liftAsmps n p = case p of
>                   By x ts ps -> By x ts (map (liftAsmps n) ps)
>                   ByAsmp m   -> ByAsmp (m + n)
>
> -- Used when we apply a proof argument.
> defAsmp :: (Int,Proof) -> Proof -> Proof
> defAsmp d@(n,p) q = case q of
>                       By x ts ps  -> By x ts (map (defAsmp d) ps)
>                       ByAsmp m | m < n      -> ByAsmp m
>                                | m > n      -> ByAsmp (m-1)
>                                | otherwise  -> p



Normalization of Rules

> trivialRule :: Rule -> Bool
> trivialRule r = all numV (fvs (rConc r))    -- axiom
>              || not (and (mapMaybe evalSide (rSides r))) -- assumes false
>              || rConc r `elem` rAsmps r   -- assumes the conclusion
>
> evalSide :: Prop -> Maybe Bool
> evalSide (Prop op [Const x, Const y, Const z])
>   | Add <- op = return (x + y == z)
>   | Mul <- op = return (x * y == z)
>   | Exp <- op = return (x ^ y == z)
> evalSide (Prop op [Const x, Const y])
>   | Eq  <- op = return (x == y)
>   | Leq <- op = return (x <= y)
> evalSide _ = mzero

See if some of the assumptions are redundant because they can be solved
with one of the fixed rules that we already know.

> normalize :: Rule -> Rule
> normalize r0 = check 0 r0 id (rAsmps r0)
>   where
>   check n r bs as =
>     case as of
>       [] -> r { rAsmps = bs [] }
>       p : ps
>        | isSide p  ->
>          check n r { rSides = p : rSides r
>                    , rProof = defAsmp (n, toProof p) (rProof r)
>                    } bs ps
>        | otherwise -> check (n+1) r ((p:) . bs) ps
>
>   toProof (Prop op ps) =
>     By (case op of
>           Add -> Thm "DefAdd" ps
>           Mul -> Thm "DefMul" ps
>           Exp -> Thm "DefExp" ps
>           Leq -> Thm "DefLeq" ps
>           Eq  -> error "Eq Asmp (this could be done by ref)"
>        ) [] []




The rules

> onlyFRules :: [Rule]
> onlyFRules = foldr addRule []
>                   (commRules ++ asmpRules ++ leqRules ++ notSymRules)

> onlyBRules :: [Rule]
> onlyBRules = axiomSchemas ++ simpleRules

> commuteConcs :: [Rule] -> [Rule]
> commuteConcs rs = rs ++ do r <- rs
>                            c <- commRules
>                            cutRule c r

> commuteAsmps :: [Rule] -> [Rule]
> commuteAsmps rs = rs ++ do r <- rs
>                            c <- commRules
>                            cutRule r c

> specSimple :: [Rule] -> [Rule]
> specSimple rs = rs ++ filter (not . trivialRule)
>                      (do r <- rs
>                          c <- axiomSchemas ++ simpleRules
>                          cutRule r c)

> srcOfVars :: (String -> Var) -> Integer -> [Term]
> srcOfVars mk from = do v <- [ from :: Integer .. ]
>                        map (Var . mk . version v) [ 'a' .. 'z' ]
>   where version 0 x = [x]
>         version n x = x : show n


> leqRules :: [Rule]
> leqRules = foldr addRule []
>          $ specSimple
>          $ commuteAsmps
>          $ map toSimpleRule
>          [ aRule "AddLeq"   [ x  +  y === z          ] (x <== z)
>          , aRule "MulLeq"   [ x  *  y === z, 1 <== y ] (x <== z)
>          , aRule "ExpLeq1"  [ x ^^^ y === z, 1 <== y ] (x <== z)
>          , aRule "ExpLeq2"  [ x ^^^ y === z, 2 <== x ] (y <== z)
>          ]
>   where
>   x : y : z : _ = srcOfVars V 0


Definition schemas for basic functions and relations

> axiomSchemas :: [Rule]
> axiomSchemas = map toSimpleRule
>   [ rule "DefAdd" (x  +  y === z)
>   , rule "DefMul" (x  *  y === z)
>   , rule "DefExp" (x ^^^ y === z)
>   , rule "DefLeq" (x <== y)
>   ]
>   where x : y : z : _ = srcOfVars NV 0

> simpleRules :: [Rule]
> simpleRules = commuteConcs $ map toSimpleRule $
>   [ rule "LeqRefl" (x <== x)
>   , rule "Leq0"    (0 <== x)
>   , rule "Add0"    (x  +  0  === x)
>   , rule "Mul0"    (x  *  0  === 0)
>   , rule "Mul1"    (x  *  1  === x)
>   , rule "Root0"   (x ^^^ 0  === 1)
>   , rule "Root1"   (x ^^^ 1  === x)
>   , rule "Log1"    (1 ^^^ x  === 1)
>   ]
>   where x : _ = srcOfVars V 0

Also, perhaps:
log_0 = (0 ^ x = y)  <=>  (y <= 1)


Commutativity

> commRules :: [Rule]
> commRules = map toSimpleRule
>   [ rule "AddComm" (x + y === y + x)
>   , rule "MulComm" (x * y === y * x)
>   ]
>   where x : y : _ = srcOfVars V 0


> asmpRules :: [ Rule ]
> asmpRules =
>     foldr addRule [] $
>     specSimple $
>     funs ++
>     map toSimpleRule (
>     [ aRule "SubL"     [ x1  +  y  === x2  +  y           ] (x1 === x2)
>     , aRule "SubR"     [ x   + y1  === x   +  y2          ] (y1 === y2)
>     , aRule "DivL"     [ x1  *  y  === x2  *  y,  1 <== y ] (x1 === x2)
>     , aRule "DivR"     [ x   * y1  === x   *  y2, 1 <== x ] (y1 === y2)
>     , aRule "Root"     [ x1 ^^^ y  === x2 ^^^ y,  1 <== y ] (x1 === x2)
>     , aRule "Log"      [ x  ^^^ y1 === x  ^^^ y2, 2 <== x ] (y1 === y2)
>     , aRule "LeqAsym"  [ x <== y, y <== x ]                 (x === y)
>     , aRule "LeqTrans" [ x <== y, y <== z ]                 (x <== z)
>     ]
>     )
>   where
>   x : x1 : x2 : y : y1 : y2 : z : z1 : z2 : _ = srcOfVars V 0
>
>   funs = do (op,name) <- [ (Add,"Add"), (Mul,"Mul"), (Exp,"Exp") ]
>             return $ mkRule ("Fun" ++ name)
>                    [Prop op [x,y,z1], Prop op [x,y,z2]]
>                    (Prop Eq [z1,z2])
>




> notSymRules :: [Rule]
> notSymRules = foldr addRule []
>             $ specSimple
>             $ map toSimpleRule
>             $ concatMap makeSym
>
>   -- Associativity
>   [ rule "AddAssoc" $ (x + y) + z === x + (y + z)
>   , rule "MulAssoc" $ (x * y) * z === x * (y * z)
>
>   -- Distributivity
>   , rule "AddMul" $ (x + y)  *  z === x  *  z + y *   z
>   , rule "MulExp" $ (x * y) ^^^ z === x ^^^ z * y ^^^ z
>
>   -- Exponentiation
>   , rule "ExpAdd" $ x ^^^ (y + z) === x ^^^ y * x ^^^ z
>   , rule "ExpMul" $ x ^^^ (y * z) === (x ^^^ y) ^^^ z
>   ]
>   where
>   x : y : z : _ = srcOfVars V 0
>   makeSym r = r : case r of
>                     RuleHL n as (Prop Eq [p,q])
>                       -> [ RuleHL (n ++ "Sym") as (Prop Eq [q,p]) ]
>                     _ -> []





------------------------------------------------------------------------------


Cut

A1,a => B
A2 => a
------------
A1,A2 => B

> cutRule :: Rule -> Rule -> [Rule]
> cutRule rfun0 rarg =
>   do let vs      = fvs rarg
>          new     = length (rAsmps rarg)   -- new param for 'rfun'
>          rfun    = fresh vs rfun0
>      (((n,asmp),rest)) <- choose (zip [ new .. ] (rAsmps rfun))
>      su <- mgu asmp (rConc rarg)
>
>          -- Add params to be used for the argument
>      return $ apSubst su rfun
>                   { rAsmps = rAsmps rarg ++ map snd rest
>                   , rSides = nub (rSides rarg ++ rSides rfun)
>                   , rProof = defAsmp (n, rProof rarg)
>                            $ liftAsmps new (rProof rfun)
>                   }


Symmetry of equality

A => x = y
----------
A => y = x


XXX: How do we instantiate this?

> eqSym :: Rule -> Maybe Rule
> eqSym r = case rConc r of
>             Prop Eq [x,y] ->
>                return r { rConc  = Prop Eq [y,x]
>                         , rProof = error "unused"
>                         }
>             _ -> mzero


------------------------------------------------------------------------------
Substitution


> type Subst = [ (Var, Term) ]
>
> class FVS t where
>   fvs     :: t -> [Var]
>   apSubst :: Subst -> t -> t

> class FVS t => Match t where
>   match   :: t -> t -> [Subst]
>   mgu     :: t -> t -> [Subst]

Merges two substitutions as long as they agree on all common variables.

> merge :: MonadPlus m => Subst -> Subst -> m Subst
> merge su = validate
>   where validate [] = return su
>         validate ((x,t) : xs) = case lookup x su of
>                                   Nothing -> do ys <- validate xs
>                                                 return ((x,t) : ys)
>                                   Just t' -> guard (t == t') >> validate xs

Composes two substitutions (function composition order).

> compose :: Subst -> Subst -> Subst
> compose s2 s1 = [ (x, apSubst s2 t) | (x,t) <- s1 ] ++
>                 [ (x,t) | (x,t) <- s2, x `notElem` map fst s1 ]


Rename a variable so that it is different from a set of given names.

> pickName :: [Var] -> Var -> Var
> pickName ks nm = if nm `elem` ks then pickName ks new else nm
>   where
>   new = case nm of
>           V x  -> V (modify x)
>           NV x -> NV (modify x)
>   modify x = x ++ "'"
>
> pickNames :: [Var] -> [Var] -> [Var]
> pickNames avoid (x : xs) = let x' = pickName avoid x
>                            in x' : pickNames (x' : avoid) xs
> pickNames _ []  = []

> fresh :: FVS a => [Var] -> a -> a
> fresh as t = apSubst (concat (zipWith toBind vs (pickNames as vs))) t
>   where toBind x x' = [ (x, Var x') ]
>         vs          = fvs t

> unions :: [[Var]] -> [Var]
> unions = nub . concat
>
> instance (FVS a, FVS b) => FVS (a,b) where
>   fvs (x,y)         = union (fvs x) (fvs y)
>   apSubst s (x,y)   = (apSubst s x, apSubst s y)
>
> instance (Match a, Match b) => Match (a,b) where
>   match (a,b) (x,y) = do su1 <- match a x
>                          su2 <- match b y
>                          merge su1 su2
>   mgu (a,b) (x,y)   = do su1 <- mgu a x
>                          su2 <- mgu (apSubst su1 b) (apSubst su1 y)
>                          return (compose su2 su1)

> instance FVS a => FVS [a] where
>   fvs         = unions . map fvs
>   apSubst s   = map (apSubst s)
>
> instance (Match a) => Match [a] where
>   match [] []         = return []
>   match (x:xs) (y:ys) = match (x,xs) (y,ys)
>   match _ _           = mzero
>
>   mgu [] []           = return []
>   mgu (x:xs) (y:ys)   = mgu (x,xs) (y,ys)
>   mgu _ _             = mzero


> instance FVS Term where
>   fvs term =
>     case term of
>       App _ t1 t2 -> fvs [ t1, t2 ]
>       Var x       -> [ x ]
>       Const _     -> []
>
>   apSubst su term =
>     case term of
>       Var v -> case lookup v su of
>                  Nothing -> term
>                  Just t  -> t
>       App op t1 t2  -> App op (apSubst su t1) (apSubst su t2)
>       Const _       -> term
>
>
> instance Match Term where
>   match (Var v) t  = case (v,t) of
>                            (NV _, Var (V _)) -> mzero
>                            _                 -> return [(v,t)]
>   match (Const x) (Const y) | x == y  = return []
>   match (App op1 s1 t1) (App op2 s2 t2)
>     | op1 == op2 = match (s1,t1) (s2,t2)
>   match _ _ = mzero
>
>   mgu (Var x) t = bindVar x t
>   mgu t (Var x) = bindVar x t
>   mgu (Const x) (Const y) | x == y  = return []
>   mgu (App op1 s1 t1) (App op2 s2 t2)
>     | op1 == op2 = mgu (s1,t1) (s2,t2)
>   mgu _ _ = mzero

> bindVar :: MonadPlus m => Var -> Term -> m Subst
> bindVar x (Var y) | x == y      = return []
> bindVar x t | x `elem` fvs t    = mzero
> bindVar x@(NV {}) t | isNum t   = return [(x,t)]
>                     | otherwise = mzero
>   where isNum (Var (NV {})) = True
>         isNum (Const _)     = True
>         isNum _             = False
> bindVar x t                   = return [(x,t)]



> instance FVS Prop where
>   fvs (Prop _ ts)         = fvs ts
>
>   apSubst su (Prop op ts) = Prop op (apSubst su ts)
>
>
> instance Match Prop where
>   match (Prop op ts) (Prop op' ts') | op == op' = match ts ts'
>   match _ _ = mzero
>
>   mgu (Prop op ts) (Prop op' ts') | op == op' = mgu ts ts'
>   mgu _ _ = mzero

> instance FVS Rule where
>   fvs r = fvs ((rAsmps r, rSides r), rConc r)
>   apSubst s r = normalize r { rAsmps = apSubst s (rAsmps r)
>                             , rSides = apSubst s (rSides r)
>                             , rConc  = apSubst s (rConc r)
>                             , rProof = apSubst s (rProof r)
>                             }
>
> instance Match Rule where
>   match r1 r2 =
>     do sRes  <- match (rConc r1) (rConc r2)
>        sSi   <- matchSet (rSides r1) (rSides r2)
>        sCons <- matchSet (rAsmps r1) (rAsmps r2)
>        merge sSi =<< merge sRes sCons
>
>   mgu r1 r2 =
>     do s1 <- mgu (rConc r1) (rConc r2)
>        s2 <- mguSet (apSubst s1 (rSides r1)) (apSubst s1 (rSides r2))
>        let s3 = compose s2 s1
>        s4 <- mguSet (apSubst s3 (rAsmps r1)) (apSubst s3 (rAsmps r2))
>        return (compose s4 s3)

== Matching ==

Matching checks if one structure is "more general" than another, in the
sense that if "match t1 t2 = Just s", then "apSubst s t1 == t2".

One way to think of this is as if the left term is a pattern.
Then, matching checks if the given pattern (i.e., the first argument)
would accept the given term (i.e., second argument).
The resulting substitution contains the bindings of the pattern variables.


Match two lists of equations, disregarding the order.

> matchSet :: [Prop] -> [Prop] -> [Subst]
> matchSet [] []      = return []
> matchSet (x:xs) zs  = do (y,ys) <- choose zs
>                          match (x,xs) (y,ys)
> matchSet _ _        = mzero


> mguSet :: [Prop] -> [Prop] -> [Subst]
> mguSet [] []      = return []
> mguSet (x:xs) zs  = do (y,ys) <- choose zs
>                        mgu (x,xs) (y,ys)
> mguSet _ _        = mzero





do s <- match (A => B) (X => Y)
   assert (apSubst s (A => B) == (X => Y)

Therefore, the rule "A => B" is more general then "X => Y",
because we can always instantiate "A => B" with "s" to obtain "X => Y".

However, this is not entirely true because of "side conditions".
Consider the following two rules:

(a + b = c, x + y = z)      => y = b

(nA + nB = nC, nA + y = nC) => y = nB

Clearly we can instantiate the first rule to get the second one
(in fact, we obtained the second one by specialzing the first!).

However, the second is different to the first in that it allows us
to do some computation on known constants.  Indeed, the second rule
really has the form:

(nA + y + nC) => y = nB     // as long as nA + nB = nC


> betterRuleThen :: Rule -> Rule -> Bool
> r1 `betterRuleThen` r2'  =
>   let r2 = fresh (fvs r1) r2'
>   in warn $
>      not $ null $ match r1 r2 ++ (match r1 =<< maybeToList (eqSym r2))
>
>   where
>   warn b
>     | b = trace ("Sumbsumed:")
>         $ trace (" New: " ++ show r1)
>         $ trace (" Old: " ++ show r2')
>         $ b
>     | otherwise = False




> addRule :: Rule -> [Rule] -> [Rule]
> addRule r rs = if any (`betterRuleThen` r) rs
>                   then rs
>                   else r : filter (not . (r `betterRuleThen`)) rs



Existentials

(a + b = x, x + c = z)
=>
exists y. (b + c = y, a + y = z)

Now, if we also have @a + p = z@, then by cancellation we
learn that "y = p", and hence we have a new fact @b + c = p@, without
having to introduce new variables.


The situation is simillar for multiplication except that, in that case,
we also need to consider the side conditions:

(a * b = x, x * c = z)
=>
exists y. (b * c = y, a * y = z)

So, now if we have @a * p = z@, we can only conclude that "p = y" if
we also know that "1 <= a".  So the complete combined rule is:

(a * b = x, x * c = z, a * p = z, 1 <= a)
=>
b * c = p


How do we obtain the rule with existential quantifier?

The basic rule is based on the fact that all our functions are total:

forall x y. exists z. x * y = z

So:
proof: (A: a * b = x, B: x * c = z, F : a * p = z, G : 1 <= a) -> (b * c = p)

  let C : exists y. b * c = y
      C = total_* [b,c]

      D : b * c = !y
      D = exist_elim C

      E : a * !y = z
      E = assoc (A,B,D)

      H : !y = p
      H = cancel_* (E,F,G)

  in subst H D
---

--------------------------------------------------------------------------------






Showing

> ppProof :: Proof -> Doc
> ppProof r0 =
>   case r0 of
>     ByAsmp n -> char '?' <> int n
>     By x ts ps ->
>       ppTheorem x <> (if null ts then empty else char '@' <>
>                       parens (hsep $ punctuate comma $ map (text . show) ts))
>       $$ nest 2 (vcat (map ppProof ps))
>
> ppTheorem :: Theorem -> Doc
> ppTheorem (Thm x [])  = text x
> ppTheorem (Thm x ts)  = parens (text x <+> fsep (map (text . show) ts))


> instance Show Var where
>   show (V x)  = x
>   show (NV x) = "num_" ++ x
>
> instance Show Prop where
>   show (Prop op [t1,t2,t3]) =
>                             unwords [show t1, show op, show t2,"==",show t3]
>   show (Prop r [t1,t2]) =  unwords [show t1, show r, show t2]
>   show (Prop c ts)      = unwords (show c : map show ts)
>
> instance Show Op where
>   show op = case op of
>               Add -> "+"
>               Mul -> "*"
>               Exp -> "^"
>               Eq  -> "=="
>               Leq -> "<="
>
> instance Show Term where
>   show (Var x)        = show x
>   show (Const n)      = show n
>   show (App op t1 t2) = "(" ++ unwords [ show t1, show op, show t2 ] ++ ")"
>
> instance Show Rule where
>   show r = case rAsmps r of
>              [] -> show (pp (rConc r) <+> sides)
>              xs -> show $ parens (hsep (punctuate comma $ map pp xs))
>                          <+> text "=>" <+> pp (rConc r) <+> sides
>     where pp = text . show
>           sides = case rSides r of
>                     [] -> empty
>                     ss -> text "//" <+> hsep (punctuate comma (map pp ss))


> ppLongRule :: Rule -> Doc
> ppLongRule r = case (rProof r, rAsmps r, rSides r) of
>                  (By _ _ _,as,ss) ->
>                     vcat (zipWith ppAsmp [0..] as) $$
>                     vcat [ text "//" <+> pp s | s <- ss ] $$
>                     text "-------------------------" $$
>                     ppConc (rProof r) (rConc r)
>                  (ByAsmp _, _, _) -> error "ppLongRule: ByAsmp"
>   where pp x = text (show x)
>         ppAsmp n v = int n <> char ':' <+> pp v
>         ppConc p v = ppProof p $$ (text ":" <+> pp v)
>
> ppLongRules :: [Rule] -> Doc
> ppLongRules rs = vcat $ punctuate (text "\n") $ map ppLongRule rs


== Terms to SimpleTerms ==

> data S      = S { names :: !Int
>                 , known :: !(M.Map (Op, Term, Term) Term)
>                 , eqs   :: [(Var,Term)]
>                 , leqs  :: [(Term,Term)]
>                 }
>
> initS      :: S
> initS       = S { names = 0, known = M.empty, eqs = [], leqs = [] }
>
> type M a = State S a
>
> getVar :: Op -> Term -> Term -> M Term
> getVar op t1 t2 =
>       do s <- get
>          let m = known s
>              su = eqs s
>              k = (op,apSubst su t1, apSubst su t2)
>          case M.lookup k m of
>            Just v  -> return v
>            Nothing ->
>              do let i = names s
>                     v = Var $ V ("aa" ++ show i)
>                 set s { names = 1 + i
>                       , known = M.insert k v m
>                       }
>                 return v
>
> addRel :: Op -> Term -> Term -> M ()
> addRel r t1 t2 =
>   do s <- get
>      let su = eqs s
>          x1 = apSubst su t1
>          x2 = apSubst su t2
>
>      case r of
>        Eq ->
>         case mgu x1 x2 of
>           [su1] -> set $ s { eqs = compose su1 su }
>           _     -> error $ "bug: We assumed False: " ++ show x1 ++
>                                               " /= " ++ show x2
>
>        Leq ->
>         case (x1,x2) of
>           (Const x, Const y)
>             | x <= y   -> return ()
>             | otherwise -> error $ "bug: We assumed False: "
>                                                 ++ show x ++ " > " ++ show y
>           (Const 0, _) -> return ()
>           (x, y) -> set $ s { leqs = (x,y) : leqs s }
>
>        _ -> error $ "bug: addRel, not a rel: " ++ show r
>
>
> run :: FVS a => M a -> (a, [Prop])
> run m =     (apSubst su a
>             , do (t1,t2) <- leqs finS
>                  return $ apSubst su $ Prop Leq [t1,t2]
>               ++
>               do ((op,t1,t2), x) <- M.toList (known finS)
>                  return $ apSubst su $ Prop op [t1,t2,x]
>             )
>   where (a,finS) = runS m initS
>         su       = eqs finS
>
> toSimple :: Term -> M Term
> toSimple te =
>   case te of
>     Const i       -> return (Const i)
>     Var x         -> return (Var x)
>     App op t1 t2  -> do t1' <- toSimple t1
>                         t2' <- toSimple t2
>                         getVar op t1' t2'
>
> toSimpleProp :: Prop -> M Prop
> toSimpleProp (Prop Eq [App op t1 t2, t3]) = toSimpleProp (Prop op [t1,t2,t3])
> toSimpleProp (Prop Eq [t3, App op t1 t2]) = toSimpleProp (Prop op [t1,t2,t3])
> toSimpleProp (Prop op ts) =
>   do xs <- mapM toSimple ts
>      return (Prop op xs)
>
>
> addAsmp :: Prop -> M ()
> addAsmp (Prop r [t1,t2]) | r `elem` [Eq,Leq] =
>   do x1 <- toSimple t1
>      x2 <- toSimple t2
>      addRel r x1 x2
>
> addAsmp eqn@(Prop r _) | r `elem` [Add,Mul,Exp] =
>   do Prop op [x1,x2,x3] <- toSimpleProp eqn
>      x4 <- getVar op x1 x2
>      addRel Eq x3 x4
>
> addAsmp _ = error "addAsmp: I don't know how to simplify this"

>
> toSimpleRule :: RuleHL -> Rule
> toSimpleRule (RuleHL name as c) = mk $ run $ do mapM_ addAsmp as
>                                                 toSimpleProp c
>   where mk (x,y) = mkRule name y x

> choose :: [a] -> [(a,[a])]
> choose [] = []
> choose (x : xs) = (x, xs) : [ (y, x:ys) | (y,ys) <- choose xs ]



== Eliminating Non-linear Patterns ==

The goal here is to replace repeated variables with explicit equatiuns.
This is useful when we intend to use a rule as a Haskell pattern.

For example:

x + 0 = x

becomes

x + 0 = x' | x == x'


> data PatS = PatS { patProps  :: [Prop]            -- Equations between vars
>                  , patKnown :: [Var]            -- Bound vars
>                  }
>
> initPatS :: PatS
> initPatS = PatS { patProps = [], patKnown = [] }
>
> type PatM = State PatS
>
>
> class NonLin t where
>   nonLin :: t -> PatM t
>
> instance NonLin Var where
>   nonLin v =
>     do s <- get
>        let m = patKnown s
>            v1 = pickName m v
>        when (v1 /= v) $
>          set s { patProps = Prop Eq [Var v, Var v1] : patProps s }
>        sets_ $ \s1 -> s1 { patKnown = v1 : m }
>        return v1
>
> instance NonLin a => NonLin [a] where
>   nonLin = mapM nonLin
>
> instance NonLin Term where
>   nonLin (Var x)       = Var `fmap` nonLin x
>   nonLin (Const x)     = return (Const x)
>   nonLin (App op t1 t2)= App op `fmap` nonLin t1 `ap` nonLin t2
>
> instance NonLin Prop where
>   nonLin (Prop op ts) = Prop op `fmap` mapM nonLin ts
>
> rmNonLin :: NonLin a => (a -> [Prop] -> b) -> a -> b
> rmNonLin k x = k a (patProps finS)
>   where (a,finS) = runS m initPatS
>         m        = nonLin x



== Constraint to Definitional Equations ==

Exmaple:

Define "x" from:

x * 5 = y

results in:

Just x <- divide y 5


> data Defn = Def { defPartial :: Bool
>                 , defOp      :: String
>                 , defArg1    :: Term
>                 , defArg2    :: Term
>                 } deriving Eq
>
> instance FVS Defn where
>   fvs d = fvs (defArg1 d, defArg1 d)
>   apSubst s d = d { defArg1 = apSubst s (defArg1 d)
>                   , defArg2 = apSubst s (defArg2 d)
>                   }


> scDefs :: Prop -> [ (Var, Defn) ]
> scDefs (Prop op [x1,x2,x3])
>   | Add <- op = opList "minus"        "minus"       "(+)"
>   | Mul <- op = opList "divide"       "divide"      "(*)"
>   | Exp <- op = opList "descreteRoot" "descreteLog" "(^)"
>   where
>   opList l r o =
>     [ (x, Def True  l x3 x2) | Var x@(NV _) <- [x1] ] ++
>     [ (x, Def True  r x3 x1) | Var x@(NV _) <- [x2] ] ++
>     [ (x, Def False o x1 x2) | Var x@(NV _) <- [x3] ]
>
> -- We could add a rule for "=", but is it neccessary?
> scDefs _  = []



== Sovlver Rules ==


"Forward" rules are used when we add a new fact to the set of assumptions.
They combine the existing assumptions with the new fact to derive more facts.

> data FRule = FRule
>   { fPats   :: Props        -- Existing assumptions
>   , fAdding :: (Int,Prop)   -- New assumption, and it's position in arg
>   , fGuards :: [ Guard ]    -- Side conditions
>   , fBoringGs :: [ Guard ]  -- Uninteresting equality side conditions
>   , fNew    :: Prop         -- Derived fact
>   , fProof  :: Proof        -- Proof of the derived fact
>   , fNotes  :: Doc          -- Additional comments
>   }


"Backward" rules are used to solve a goal, from a set of assumptions.

> data BRule = BRule
>   { bPats     :: [ Prop ]   -- Existing assumptions
>   , bGuards   :: [ Guard ]  -- Side conditions
>   , bBoringGs :: [ Guard ]  -- Uninteresting equality side conditions
>   , bProof    :: Proof      -- Proof for the new fact
>   , bNew      :: Prop       -- Fact that can be solved
>   , bNotes    :: Doc
>   }

"Guards" or side-conditions restrict when a set of equations are suitable for
something.  They differ from other equations in that we don't need to match
them against existing assumptions, because they do not contain unbaound
variables.

> data Guard = GBool Prop | GPat Var Defn
>   deriving Eq
>
> instance FVS Guard where
>   fvs (GBool eq)  = fvs eq
>   fvs (GPat _ d)  = fvs d
>
>   apSubst s (GBool eq)  = GBool (apSubst s eq)
>   apSubst s (GPat x d)  = GPat x (apSubst s d)
>
> {-
>   match (GBool e1) (GBool e2) = match e1 e2
>   match (GPat {}) (GPat {})   = mzero -- XXX: What do we do here (binders)
>   match _ _ = mzero
> -}
>
>
> instance Show Guard where
>   show (GBool e) = show e
>   show (GPat x d)
>     | defPartial d =
>         unwords $ [ "Just", show x, "<-" ] ++ expr
>     | otherwise =
>         unwords $ [ "let", show x, "=" ] ++ expr
>     where expr = [ defOp d, show (defArg1 d), show (defArg2 d) ]

> instance NonLin FRule where
>   nonLin r =
>     do ps <- mapM nl (propsToList (fPats r))
>        a  <- nl (fAdding r)
>        return r { fPats = propsFromList ps, fAdding = a }
>     where nl (x,p) = do p1 <- nonLin p
>                         return (x,p1)
>
> instance NonLin BRule where
>   nonLin r =
>     do ps <- nonLin (bPats r)
>        a  <- nonLin (bNew r)
>        unless (null $ intersect (fvs ps) (fvs a)) $ error "non-lin bug"
>        return r { bPats = ps, bNew = a }


We know that while type checking we never have assumptions
with two constants in the environemnt, because those would have
been simplified.  For example, we would not find "3 + 5 = x" as
an assumption becuase this would have been simplified to "x = 8".
For this reason, when we have a rule with such an assumption
in the environment we try to rewrite the assumption as a Haskell guard.
This works as long as there is another assumption that mentions the
variable, so that the variale is defined somewhere.

For example:

(X + 5 = Y, P(Y)) => Q(X)

becomes:

P(Y)
  | Just X <- minus Y 5   => Q(X)



> resolveGuards :: [Var] -> [Var] -> [Prop] -> Maybe [Guard]
> resolveGuards def0 needDef0 gs0 =
>   listToMaybe (loop def0 needDef0 [] [] False gs0)
>   where
>   loop defined needDef done delayed changes []
>     | not changes = do guard (all (`elem` defined) needDef && null delayed)
>                        return (reverse done)
>     | otherwise   = loop defined needDef done [] False delayed
>
>   loop defined needDef done delayed changes (g : gs) =
>     case fvs g \\ defined of
>       -- All variables are defined, done with this one.
>       [] -> loop defined needDef (GBool g : done) delayed changes gs
>       xs ->
>           -- try to define one of the vars using the guard
>           do (x,d) <- scDefs g
>              guard (x `elem` xs)
>              loop (x:defined) (fvs d ++ needDef) (GPat x d : done)
>                                                           delayed True gs
>           ++ -- ... or if that did not work, then wait to see if some
>              -- other guard might define our variables.
>           loop defined needDef done (g : delayed) changes gs






Convert a rule into one suitable for forward reasoning:

(R,r) => p

If we already know "R", and then we add "r" to it, we can
construct a new fact "p".  All the variables in "p" should
be defined in terms of variables in "R" and "r".

> {-
> toFRule' :: Rule -> [((Int,Prop), [(Int,Prop)])]
> toFRule' r =
>   -- foldr addFRule [] $
>   do (x,xs) <-
>      return (x, r { rAsmps = map snd xs })
>
> sameFRule :: [Var] -> (Prop, Rule) -> (Prop,Rule) -> Bool
> sameFRule vs1 f1 f2' =
>   let f2@(e2,r2) = fresh vs1 f2'
>   in not $ null $ match f1 f2 ++
>                   ((\z -> match f1 (e2,z)) =<< maybeToList (eqSym r2))
>
> addFRule :: (Prop,Rule) -> [(Prop,Rule)] -> [(Prop,Rule)]
> addFRule x xs = if any (sameFRule (fvs x) x) xs then xs else x : xs
> -}


> toFRule :: Rule -> [FRule]
> toFRule r =
>   do (e,rs) <- choose $ zip [ 0 .. ] (rAsmps r)
>      gs <- maybeToList
>          $ resolveGuards (fvs (snd e,map snd rs))
>                          (fvs (rConc r))
>                          (rSides r)
>
>      return FRule { fPats   = propsFromList rs
>                   , fAdding = e
>                   , fBoringGs  = []
>                   , fGuards = gs
>                   , fNew    = rConc r
>                   , fProof  = rProof r
>                   , fNotes  = text "Adding" <+> int (fst e)
>                            $$ ppLongRule r
>                   }


Convert a rule into one suitable for backward reasoning (i.e., solving things).

> toBRule :: Rule -> [BRule]
> toBRule (Rule { rConc = Prop Eq _ }) = []  -- we relay on frules to fire
> toBRule r =
>   do let y      = rConc r
>          guards = rSides r
>          pats   = rAsmps r

>      hsGuards <-
>        case resolveGuards (fvs (y,pats)) [] guards of
>          Nothing -> trace ("BRule: failed to resolve guards for: "
>                                                           ++ show r) mzero
>          Just t -> return t
>
>      return BRule { bPats   = pats, bNew = y
>                   , bGuards = hsGuards, bBoringGs =[]
>                   , bProof  = rProof r
>                   , bNotes  = ppLongRule r
>                   }


> solverRules :: ([FRule], [BRule])
> solverRules = ( concat (map mkFRule onlyFRules)
>               , concat (map mkBRule onlyBRules)
>               )
>   where
>   mkFRule = map (rmNonLin forFRule) . toFRule
>   mkBRule = map (rmNonLin forBRule) . toBRule
>
>   forFRule f es = f { fBoringGs = map GBool es }
>   forBRule f es = f { bBoringGs = map GBool es }




== To Haskell ==

> type Pat = Doc
>
> conPat :: String -> [Pat] -> Pat
> conPat n [] = text n
> conPat n ps = text n <+> fsep ps
>
> numPat :: Pat -> Pat
> numPat p    = conPat "Num" [ p, wildPat ]
>
> wildPat :: Pat
> wildPat = char '_'
>
> tuplePat :: [Pat] -> Pat
> tuplePat ps = parens $ fsep $ punctuate comma ps
>
> listPat :: [Pat] -> Pat
> listPat = smallList

> smallList :: [Doc] -> Doc
> smallList = brackets . hsep . punctuate comma

> bigList :: [Doc] -> Doc
> bigList [] = text "[]"
> bigList (x : xs) = (text "[" <+> x) $$
>                   vcat [ comma <+> y | y <- xs ] $$
>                   text "]"

> ppGuards :: [Guard] -> [Guard] -> Doc
> ppGuards bore gs =
>   case (map pp bore, map pp gs) of
>     ([], []) -> empty
>     ([], is) -> interesting (char '|') is
>     (bs, is) -> boring bs $$ interesting comma is
>   where pp = text . show
>         boring bs = char '|' <+> hsep (punctuate comma bs)
>         interesting c (x : xs) = (c <+> x) $$ vcat (map (comma <+>) xs)
>         interesting _ _        = empty


> termToPat :: Term -> Pat
> termToPat (Var x) | not (numV x)  = text (show x)
> termToPat t                       = parens (numPat (text (show t)))
>
> eqnToPat :: Prop -> Pat
> eqnToPat (Prop op ts) = conPat "Prop" [ conPat (opCon op) []
>                                       , listPat (map termToPat ts)
>                                       ]
> opCon :: Op -> String
> opCon op =
>   case op of
>     Add -> "Add"
>     Mul -> "Mul"
>     Exp -> "Exp"
>     Leq -> "Leq"
>     Eq  -> "Eq"
>
> eqnsToPat :: [Prop] -> Pat
> eqnsToPat es  = listPat (map eqnToPat es)
>
> toExpr :: Term -> Doc
> toExpr t =
>   case t of
>     Var x | not (numV x) -> text (show x)
>     _ -> parens (text "num" <+> text (show t))
>
> eqnToExpr :: (Int -> Maybe Int) -> Proof -> Prop -> Doc
> eqnToExpr lkpParam p (Prop op ts) =
>     text "Fact" <+>
>       (text "{" <+> text "factProof =" <+> proofToExpr lkpParam p
>       $$ comma  <+> text "factProp = Prop" <+> text (opCon op)
>                                   <+> smallList (map toExpr ts)
>       $$ text "}")
>
> proofToExpr :: (Int -> Maybe Int) -> Proof -> Doc
> proofToExpr lkp (By x ts ps) =
>   hang (text "Using" <+> ppTheorem x <+> smallList (map toExpr ts)) 2
>        (bigList (map (proofToExpr lkp) ps))
> proofToExpr lkp (ByAsmp m) =
>   case lkp m of
>     Nothing -> text "new_proof"
>     Just n  -> text "proof" <> int n
>
> bruleToAlt :: BRule -> Doc
> bruleToAlt r = text "{-" <+> bNotes r <+> text "-}"
>               $$ eqnsToPat (bNew r : bPats r)
>               $$ nest 2 (ppGuards (bBoringGs r) (bGuards r)
>               $$ text "->" <+> text "Just" <+>
>                     parens (proofToExpr bindAsmps (bProof r)))
>   where bindAsmps _ = Nothing -- XXX: Implement this to use brules with
>                               -- assumptions.
>
> solveFun :: (Int, [BRule]) -> Doc
> solveFun (_,[]) = error "bug: solveFun []"
> solveFun (n, bs) =
>     text "solve" <> int n <+> text ":: [Fact] -> Prop -> Maybe Proof" $$
>     text "solve" <> int n <+> text "asmps" <+> text "goal" <+> text "=" $$
>   nest 2 (text "case goal : map factProp asmps of"
>           $$ nest 2 (vsep (map bruleToAlt bs) $$ text "_ -> Nothing"))


> main :: IO ()
> main = main1

> main1 :: IO ()
> main1 = writeFile "TcTypeNatsRules.hs" $ show $
>   text "-- WARNING: This file is generated automatically!" $$
>   text "-- WARNING: Do not add interesting changes, as they will be lost." $$
>   text "--"
>   $$ text "-- Stats:"
>   $$ text "--"
>   $$ vcat (map (ppStats "solve") solveFuns)
>   $$ text "--"
>   $$ vsep (map ppFStats $ M.toList groupedFs)
>   $$ text "--"
>   $$ text "-- Back rules"
>   $$ vsep (map solveFun solveFuns)
>   $$ text "\n\n-- Forward rules"
>   $$ codeFRules groupedFs
>   where
>   (frs,brs) = solverRules
>   solveFuns = groupLens bPats brs
>   ppStats x (n,as)  = text "--" <+> text x <> int n
>                       <+> int (length as) <+> text "cases"
>   groupedFs = groupFRules frs

> type FRulesForOp = M.Map [(Op,Int)] [FRule]

> groupFRules :: [FRule] -> M.Map Op FRulesForOp
> groupFRules = M.map byAsmps . foldr addHead M.empty
>   where
>   addHead f     = M.insertWith (++) (pPred (snd $ fAdding f)) [f]
>   byAsmps       = foldr addAsmps M.empty
>   addAsmps f    = M.insertWith (++) key [f]
>     where key   = map cvt $ group $ sort $ map (pPred . snd) $ propsToList $ fPats f
>           cvt x = (head x, length x)
>
> ppFStats :: (Op,FRulesForOp) -> Doc
> ppFStats (k0,m) = text "-- frules for" <+> text (opCon k0)
>                  $$ vcat (map pp (M.toList m))
>   where pp (k,fs) = text "--  " <+> pad (length fs) <> text ":" <+> ppK k
>         ppK []    = text "(no asmps)"
>         ppK xs    = fsep $ punctuate comma
>                            [ int num <+> text (opCon op) | (op,num) <- xs ]
>
>         pad x     = let t = show x in text (replicate (3 - length t) ' ' ++ t)

--------------------------------------------------------------------------------


The code bellow generates functions of this form:

-- Used when the new fact is (Add t1 t2 t3), and the assumptions
-- have 2 Add, and 1 Mul.
frule_Add_2_1_0_0_0 t1 t2 t3 =
  do ((x0,x1,x2),add1) <- choose (pAdd props)
     (x3,x4,x5)        <- add1
     (x6,x7,x8)        <- pMul props
     concat [ case (t1,t2,t3,x0,x1,x2,x3,..)
                  (q1,q2,q3,p0,p1,p2,p3,...)
                    | sides -> [ rhs ]
                  _         -> []
            , case ...
            ]


> codeFRules :: M.Map Op (M.Map [(Op,Int)] [FRule]) -> Doc
> codeFRules m =
>   text "implied :: Props Fact -> Fact -> [Fact]" $$
>   text "implied" <+> fruleAsmpsName <+> text "newProp ="
>     $$ nest 2 (text "let new_proof = factProof newProp in"
>                 $$ text "case factProp newProp of" $$
>   nest 2 (vcat (map cases (M.toList m)) $$ text "_ -> []"))
>   where
>   cases (op,m1) =
>     let eqn = Prop op (take ar $ map (Var . V . fruleVar) [ 0 .. ])
>         ar  = arity op
>     in eqnToPat eqn <+> text "->" <+> text "concat"
>        $$ nest 2 (bigList
>                  $ do (_,rs) <- M.toList m1
>                       return $ text "do" <+>
>                         ( codeMatchProps ar (fPats (head rs))
>                           $$ text "concat" <+> bigList (map fruleCase rs)
>                         )
>                  )


> fruleOrder :: [Op]
> fruleOrder = [ Add, Mul, Exp, Leq, Eq ]
>
> fruleVar :: Int -> String
> fruleVar n  = "arg" ++ show n
>
> fruleAsmpsName :: Doc
> fruleAsmpsName = text "props"
>
> fruleCase :: FRule -> Doc
> fruleCase r =
>      ptext "{-" <+> fNotes r <+> text "-}"
>   $$ text "case" <+> vars <+> text "of"
>   $$ nest 2 ( tuplePat pats $$ nest 2 (ppGuards (fBoringGs r) (fGuards r)
>                             <+> text "-> return"
>                             $$ nest 2 (eqnToExpr getProofParam (fProof r) (fNew r)))
>               $$ text "_ -> mzero"
>             )
>   where
>   vars       = parens $ fsep $ punctuate comma
>                       $ take (length pats) $ map (text . fruleVar) [ 0 .. ]
>   pats       = map termToPat $ pArgs (snd $ fAdding r) ++ paramPats
>
>   (paramProofMap, paramPats)  = let (_, res) = mapAccumL doOp 1 fruleOrder
>                                     (ms,ps)  = unzip res
>                                 in (concat ms, concat ps)
>
>   doOp s op   = case M.lookup op (fPats r) of
>                   Nothing -> (s, ([],[]))
>                   Just ts -> ( s + length ts
>                              , let (ns,ps) = unzip ts
>                                in (zip ns [ s .. ], concat ps) )
>
>   getProofParam n
>     | n == fst (fAdding r) = Nothing
>     | otherwise =
>        case lookup n paramProofMap of
>          Just m  -> Just m
>          Nothing -> error
>                $ unlines ("incomplete proof"
>                          : show (ppProof (fProof r))
>                          : ("adding: " ++ show (fst (fAdding r)))
>                          : map show paramProofMap
>                          )




Generates code search for assumptions of the appropriate "shape"
(i.e., just based on the predicate, not the predicate's arguments.)

> codeMatchProps :: Int -> Props -> Doc
> codeMatchProps ar0 m = vcat $ snd $ mapAccumL doOp (ar0,1) fruleOrder
>   where
>   doOp s op = case M.lookup op m of
>                 Nothing -> (s, empty)
>                 Just ts -> step op (length ts) s
>
>   step op howMany s0 = gen howMany initSrc s0
>     where
>     initSrc   = parens (text "getPropsForRaw" <+> con <+> fruleAsmpsName)
>     nextSrc n = text "more" <> con <> int (howMany - n + 1)
>
>     pats (n,pn) = tuplePat
>                     [ listPat $ take ar [ text (fruleVar v) | v <- [ n .. ] ]
>                     , text "proof" <> int pn
>                     ]
>
>     gen 0 _  s          = (s, empty)
>     gen 1 src s@(vs,ps) = ((vs + ar, ps + 1), pats s <+> text "<-" <+> src)
>     gen n src s@(vs,ps) = let newSrc = nextSrc n
>                               (vs1, stmts) = gen (n-1) newSrc (vs+ar,ps+1)
>                    in ( vs1
>                       , tuplePat [pats s, newSrc] <+>
>                           text "<-" <+> text "choose" <+> src $$ stmts
>                       )
>     ar  = arity op
>     con = text (opCon op)



--------------------------------------------------------------------------------




> vsep :: [Doc] -> Doc
> vsep = vcat . intersperse (text " ")
>
> groupLens :: (a -> [b]) -> [a] -> [(Int,[a])]
> groupLens pats = map rearrange . groupBy same . sortBy comp . map addLen
>   where addLen x = (length (pats x), x)
>         comp = comparing fst
>         same x y = comp x y == EQ
>         rearrange xs = (fst (head xs), map snd xs)


--------------------------------------------------------------------------------


> newtype State s a = St { runS :: s -> (a,s) }
>
> instance Functor (State s) where fmap = liftM
> instance Monad (State s) where
>   return x  = St (\s -> (x,s))
>   m >>= f   = St (\s -> let (a,s1) = runS m s in runS (f a) s1)
>
> get :: State s s
> get = St (\s -> (s,s))
>
> set :: s -> State s ()
> set s = St (\_ -> ((),s))
>
> sets_ :: (s -> s) -> State s ()
> sets_ f = St (\s -> ((), f s))

--------------------------------------------------------------------------------

> type Props = M.Map Op [(Int,[Term])]
>
> noProps :: Props
> noProps = M.empty
>
> addProp :: (Int,Prop) -> Props -> Props
> addProp (n, Prop op ts) props = M.insertWith (++) op [(n,ts)] props
>
> propsToList :: Props -> [(Int,Prop)]
> propsToList props = do (op,tss) <- M.toList props
>                        (n,ts)   <- tss
>                        return (n, Prop op ts)
>
> propsFromList :: [(Int,Prop)] -> Props
> propsFromList = foldr addProp noProps




