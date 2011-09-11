{-# LANGUAGE CPP #-}
module TcTypeNats where

import Control.Monad(mzero,foldM,guard)
import Debug.Trace
import qualified Data.Map as M
import Data.List(union,find)

{-------------------------------------------------------------------------------
Terms and Propositions
-------------------------------------------------------------------------------}

type Var  = Xi

-- | The 'Xi' in the 'Num' constructor stores the original 'Xi' type that
-- gave rise to the num.  It is there in an attempt to preserve type synonyms.
data Term = Var Var
          | Num Integer (Maybe Xi)
            deriving (Eq,Ord)

data Pred = Add | Mul | Exp | Leq | Eq
            deriving (Eq, Ord)

data Prop = Prop Pred [Term]
            deriving Eq

num :: Integer -> Term
num n = Num n Nothing

instance Show Term where
  show (Var x)    = x
  show (Num x _)  = show x

instance Show Pred where
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



{-------------------------------------------------------------------------------
Sets of Propositions

Throughout the development we work with collections of propositions.
One way to represent such collections is to simply use linked lists.
However, because we often need to search for propositions
of a certain form, it is more convenient (and efficient) to group
propositions with the same predicate constructor together.
-------------------------------------------------------------------------------}

-- | We use a finite map to associate the predicate constructor for
-- each proposition with a list containing the arguments of the
-- propositions in the collection.
newtype Props = P (M.Map Pred [[Term]])

-- | Convert a set of propositions back into its list representation.
propsToList :: Props -> [Prop]
propsToList (P ps) = [ Prop op ts | (op,tss) <- M.toList ps, ts <- tss ]

-- | An empty set of propositions.
noProps :: Props
noProps = P M.empty

-- | Add a proposition to an existing set.
addProp :: Prop -> Props -> Props
addProp (Prop op ts) (P props) = P (M.insertWith union op [ts] props)

-- | Convert a list of propositions into a set.
propsFromList :: [Prop] -> Props
propsFromList = foldr addProp noProps

-- | Combine the propositions from two sets.
unionProps :: Props -> Props -> Props
unionProps (P as) (P bs) = P (M.unionWith union as bs)

-- | Pick one of the propositions from a set,
-- and return the remaining propositions.
-- Returns 'Nothing' if the set is empty.
getProp :: Props -> Maybe (Prop, Props)
getProp (P ps) =
  do ((op,t:ts),qs) <- M.minViewWithKey ps
     return (Prop op t, if null ts then P qs else P (M.insert op ts qs))

-- | Pick one of the propositions from a set in all possible ways.
chooseProp :: Props -> [(Prop,Props)]
chooseProp ps =
  case getProp ps of
    Nothing -> []
    Just (q,qs) -> (q,qs) : [ (a,addProp q as) | (a,as) <- chooseProp qs ]

-- | Get the arguments of propositions constructed with a given
-- predicate constructor.
getPropsFor :: Pred -> Props -> [[Term]]
getPropsFor op (P ps) = M.findWithDefault [] op ps

-- | Returns 'True' if the proposition belongs to the set.
elemProp      :: Prop -> Props -> Bool
elemProp (Prop op ts) (P ps) = case M.lookup op ps of
                                 Nothing  -> False
                                 Just tss -> elem ts tss

-- | Returns 'True' if the set is empty.
isEmpty :: Props -> Bool
isEmpty (P ps) = M.null ps

-- | Remove propositions that do not satisfy the given predicate.
filterProp :: (Prop -> Bool) -> Props -> Props
filterProp p (P ps) = P (M.mapMaybeWithKey upd ps)
  where upd op ts = case filter (p . Prop op) ts of
                      [] -> Nothing
                      xs -> Just xs

-- | Remove propositions with the given predicate constructor.
rmPropsFor :: Pred -> Props -> Props
rmPropsFor op (P as) = P (M.delete op as)

instance Show Props where
  show = show . propsToList


{-------------------------------------------------------------------------------
Assumptions and Goals

The solver manipulates two kinds of propositions: {\em given} propositions
correspond to assumptions that may be used without proof,
while {\em wanted} propositions correspond to goals that need to be proved.
-------------------------------------------------------------------------------}

data PropSet = PropSet { given :: Props, wanted :: Props }

emptyPropSet :: PropSet
emptyPropSet = PropSet { given = noProps, wanted = noProps }

insertGiven :: Prop -> PropSet -> PropSet
insertGiven g ps = ps { given = addProp g (given ps) }

insertWanted :: Prop -> PropSet -> PropSet
insertWanted w ps = ps { wanted = addProp w (wanted ps) }

unionPropSets :: PropSet -> PropSet -> PropSet
unionPropSets ps1 ps2 = PropSet { given  = unionProps (given ps1) (given ps2)
                                , wanted = unionProps (wanted ps1) (wanted ps2)
                                }

instance Show PropSet where
  show is = "\n" ++
            unlines [ "G: " ++ show p | p <- propsToList (given is) ] ++
            unlines [ "W: " ++ show p | p <- propsToList (wanted is) ]



{-------------------------------------------------------------------------------
Results of Entailement
-------------------------------------------------------------------------------}

{- | The entailment function may return one of three possible answers,
informally corresponding to ``certainly not'', ''not in its current form'',
and ''(a qualified) yes''. -}
data Answer = NotForAny | NotForAll | YesIf [Prop]

isNotForAny :: Answer -> Bool
isNotForAny NotForAny = True
isNotForAny _         = False

isNotForAll :: Answer -> Bool
isNotForAll NotForAll = True
isNotForAll _         = False

isYesIf :: Answer -> Bool
isYesIf (YesIf _)     = True
isYesIf _             = False




{- More precisely, \Verb"NotForAny" asserts that the proposition in question
contradicts the given set of assumptions, no matter how we instantiate its
free variables (i.e., we have a proof of the proposition's negation).
The following two examples both result in a \Verb"NotForAny" answer
(in the examples we use the more traditional mathematical notation
$ps \ent p$ for entailment)
$$
\begin{aligned}
      & \ent 2 + 3 = 6 &\mapsto~\mathtt{NotForAny}\\
x = 2 & \ent x = 3     &\mapsto~\mathtt{NotForAny}
\end{aligned}
$$
The first equation is is inconsistent with the theory in general, while the
second contradicts a particular assumption.

If the entailment function returns \Verb"NotForAll", then the proposition in
question is not entailed by the given assumptions but it also does not
contradict them.  Typically this happens when a proposition contains
free variables, and the entailment of the proposition depends on how
these variables are instantiated (e.g., some instantiations result in
propositions that are consistent with the assumptions, while others do not).
For example, consider the following entailment question:
$$
\begin{aligned}
& \ent x + y = 6     &\mapsto~\mathtt{NotForAll}
\end{aligned}
$$
This results in \Verb"NotForAll" because we cannot determine if the
proposition holds without further assumptions about $x$ and $y$---%
some instantiations (e.g., $x = 2, y = 4$)
are entailed, while others (e.g., $x = 7, y = 3$) are not.

Finally, the entailment function may give a positive answer, with an optional
list of sub-goals.  Consider the following examples:
$$
\begin{aligned}
& \ent 1 + 2 = 3 &&\mapsto~\mathtt{YesIf~[]} \\
& \ent x + 0 = x &&\mapsto~\mathtt{YesIf~[]} \\
& \ent 3 + 5 = x &&\mapsto~\mathtt{YesIf~[x=8]}
\end{aligned}
$$
The first two examples illustrate unconditional entailment, while the third
example asserts that the proposition is entailed if and only if $x = 8$ holds.
The sub-goals contained in a \Verb"YesIf" answer should be logically
equivalent to the original goal (under the given assumptions) but also
``simpler'', a concept that we shall discuss further in
Section~\ref{sec_improvement}.  -}


{-------------------------------------------------------------------------------
The Inert Set

The {\em inert set} is a collection of propositions, which keeps track
of the facts that are known by the solver, as well as any goals that
were attempted but not solved.  We refer to this set as ``inert'' because
the propositions in it cannot ``interact'' with each other.
-------------------------------------------------------------------------------}

-- | To distinguish sets with this property from other sets of propositions
-- we use a separate type synonym.
type InertSet = PropSet


-- | More formally, the following predicate captures the ``non-interacion''
-- invariant of the inert set:
inert_prop :: InertSet -> Bool
inert_prop props = all (isNotForAll . uncurry entails) $
  [ (gs, g)                   | (g, gs) <- chooseProp givens  ] ++
  [ (unionProps ws givens, w) | (w, ws) <- chooseProp wanteds ]
  where givens  = given props
        wanteds = wanted props

{- The predicate consists of two parts, both of the same form:  the first one
asserts that the collection of given facts is consistent and non-redundant,
while the second asserts the same property for the set of goals.
The ``consistent and non-redundant'' property is captured
by the requirement that when we use the entailment function we get
the answer \Verb"NotForAll"---had we obtained \Verb"NotForAny", we would
have a constradiction and hence the propositions would not be consistent,
and if we obtained \Verb"YesIf", then then the proposition would
be redundant and hence may be eliminated.  The predicate makes use
of the auxiliary function \Verb"chooseProp", which extracts a single
element from a collection in all possible ways.  -}


addGiven  :: Prop -> InertSet -> Maybe PassResult
addWanted :: Prop -> InertSet -> Maybe PassResult

data PassResult = PassResult { newInert :: Maybe InertSet -- Nothing: no change
                             , newWork  :: PropSet
                             , whatNext :: Maybe Prop -- Nothing = Solved
                             }




{-------------------------------------------------------------------------------
Adding a New Assumption (given)

When we add a new assumption to an inert set we check for ``interactions''
with the existing assumptions by using the entailment function.
-------------------------------------------------------------------------------}

addGiven g props =

  case entails (given props) g of

{- The first possibility is that the new assumption is incompatible with
the existing assumptions, in which case we simply report an error
and ignore the new fact. -}

    NotForAny -> mzero

{- Another possible outcome is that---in its current form---the proposition
is already entailed by the currently known assumptions.  Then, we leave
the inert set unmodified but we record the alternative formulation (if any)
as new work to be processed by the solver. -}

    YesIf ps -> return PassResult
      { newInert  = Nothing
      , newWork   = emptyPropSet { given = propsFromList ps }
      , whatNext  = Nothing
      }

{- Finally, if entailment yielded no interaction, then we add the new fact to
the inert set.  Any goals that were in the inert set are removed and added
back to the work queue so that we can re-process them in the context of the
new assumption. -}

    NotForAll -> return PassResult
      { newInert  = Just props { wanted = noProps }
      , newWork   = props { given = noProps }
      , whatNext  = Just g
      }


{-------------------------------------------------------------------------------
Adding a New Goal (wanted)

Extending the inert set with a new goal is a little more complex then
adding a new assumption but the overall structure of the algorithm is similar.
Again, we use the entailment function to check for interactions
between the inert set and the new goal but we also use existing goals
as assumptions.  This is useful because we may be able to discharge
the new goal in terms of already existing goals, thus leaving the inert
set unchanged.
-------------------------------------------------------------------------------}

addWanted w props =

  case entails (unionProps (wanted props) (given props)) w of

{- The first two cases---when there is interaction---are the same as for
adding an assumption:  inconsistencies result in an error, while solving
the new goal does not affect the inert set but may add a new formulation
of the goal to the work queue. -}

    NotForAny -> mzero

    YesIf ps -> return PassResult
      { newInert  = Nothing
      , newWork   = emptyPropSet { wanted = propsFromList ps }
      , whatNext  = Nothing
      }

{- The major difference in the algorithm is when there is no interaction
between the new goal and the existing inert set.  In this case we
add the new goal to the inert set but, in addition, we need to check
if it is possible to solve any of the already existing goals in terms
of the new goal.  We cannot simply add the existing goals back on the
work queue (as we did when we added an assumption) because this may
lead to a non-terminating loop:  any two goals that cannot be solved in terms
of each other are going to keep restarting each other forever.  Instead,
we examine the existing goals one at a time and check for interactions in
the presence of the new goal, removing goals that are entailed, and leaving
goals that result in no interaction in the inert set. -}

    NotForAll ->
      do let start = (noProps, noProps)
         (inert,restart) <- foldM check start (chooseProp (wanted props))

         return PassResult
           { newInert = if isEmpty restart then Nothing
                                           else Just props { wanted = inert }
           , newWork  = emptyPropSet { wanted = restart }
           , whatNext = Just w
           }

{- The function \Verb"check" has the details of how to check for interaction
between some existing goal, \Verb"w1", and the new goal \Verb"w".  The
set \Verb"ws" has all existing goals without the goal under consideration. -}

  where
  check (inert,restart) (w1,ws) =
    case entails (addProp w (unionProps ws (given props))) w1 of
      NotForAny -> mzero
      NotForAll -> return (addProp w1 inert, restart)
      YesIf ps  -> return (inert, foldr addProp restart ps)


{- To see the algorithm in action, consider the following example:

New goal:   2 <= x
Inert set:  { wanted = [1 <= x, x + 5 = y] }

Step 1: entails [1 <= x, x + 5 = y] (2 <= x)      -->  NotForAll
Step 2: Add (2 <= x) to the inert set and examine existing goals:
  Step 2.1: entails [2 <= x, x + 5 = y] (1 <= x)  --> YesIf []  // remove
  Step 2.2: entails [2 <= x, 1 <= x] (x + 5 = y)  --> NotForAll // keep

New inert set: { wanted = [2 <= x, x + 5 = y] }

-}


{-------------------------------------------------------------------------------
Entailment

A central component of the solver is the entailment function, which determines
if a set of assumptions (the first argument), entail a certain proposition
(the second argument).
-------------------------------------------------------------------------------}

entails :: Props -> Prop -> Answer

entails ps p | tr "entails?:" (propsToList ps)
             $ trace "  --------"
             $ trace ("  " ++ show p) False = undefined
entails ps' p' =
  case closure ps' of
    Nothing -> YesIf [] -- Assumed False
    Just (su,ps) ->
      let p = apSubst su p'
      in if solve ps p
            then YesIf []

            -- Try improvement
            else case closure (addProp p ps) of
                   Nothing -> NotForAny
                   Just (su1,_)

                     -- The extra facts helped
                     | solve (apSubst su1 ps) (apSubst su1 p)
                    && not (p' `elem` eqns) -> YesIf eqns

                     -- No luck
                     | p == p'   -> NotForAll

                     -- Keep going with improved proposition
                     | otherwise -> YesIf [p]
                     where eqns = substToEqns su1

closure :: Props -> Maybe (Subst, Props)
closure ps = closure1 =<< improvingSubst ps

closure1 :: (Subst, Props) -> Maybe (Subst, Props)
closure1 (su0, ps0) =
  do (su, ps) <- improvingSubst
               $ propsFromList
               $ do (q,qs) <- chooseProp ps0
                    i      <- implied qs q
                    guard (not (solve ps0 i))
                    return i

     let su1 = compose su su0
         ps1 = filterProp (not . trivial) (apSubst su ps0)

     if isEmpty ps
       then tr "computed closure:" (propsToList ps1)
           $ return (su1, ps1)
       else tr "adding:" (propsToList ps) $ closure1 (su1, unionProps ps ps1)


{-------------------------------------------------------------------------------
Proprties of the Entailment Function
-------------------------------------------------------------------------------}

-- | Adding more assumptions cannot make things less contradictory
entails_any_prop :: Props -> Prop -> Prop -> Bool
entails_any_prop ps q p =
  case entails ps q of
    NotForAny -> isNotForAny (entails (addProp p ps) q)
    _         -> True


-- | Dropping assumptions cannot make things more contradictory or more defined.
enatils_all_prop :: Prop -> Props -> Prop -> Bool
enatils_all_prop p ps q =
  case entails (addProp p ps) q of
    NotForAll -> isNotForAll (entails ps q)
    _         -> True


{-------------------------------------------------------------------------------
-- Substitutions
-------------------------------------------------------------------------------}


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


-- | Represent a substitution as a set of equations.
substToEqns :: Subst -> [Prop]
substToEqns su = [ Prop Eq [Var x, t] | (x,t) <- su ]

-- | Turn the equations that we have into a substitution, and return
-- the remaining propositions with the substitution applied to them.
-- XXX: It might be better to simply keep these equations as
-- substitutions in the 'Props' type.
improvingSubst :: Props -> Maybe (Subst, Props)
improvingSubst ps  = do su <- loop [] (getPropsFor Eq ps)
                        return (su, filterProp (not . trivial)
                                   $ apSubst su $ rmPropsFor Eq ps)
  where
  loop su ([x,y] : eqs) =
    do su1 <- mgu x y
       loop (compose su1 su) (apSubst su1 eqs)
  loop _ (_ : _) = error "bug: improveSubst eqn of arity not 2"
  loop su [] = return su



trivial :: Prop -> Bool
trivial = solve noProps

solve :: Props -> Prop -> Bool
solve  _ (Prop Eq [x,y]) | x == y = True
solve ps p = solve0 [] p || elemProp p ps




{-------------------------------------------------------------------------------
Testing without GHC
-------------------------------------------------------------------------------}

#define TEST_WITHOUT_GHC 1
#ifdef TEST_WITHOUT_GHC

type Xi   = String

eqType :: Xi -> Xi -> Bool
eqType = (==)

{-------------------------------------------------------------------------------
The Solver

The purpose of the solver is to turn an arbitrary set of propositions
into an inert one.  This is done by starting with some inert set
(e.g., the empty set of propositions) and then adding each new proposition
one at a time.  Assumptions and goals are added in different ways, so
we have two different functions to add a proposition to an existing
inert set.

If successful, both functions return a \Verb"PassResult" value, which
contains an updated inert set and, potentially, some additional propositions
that need to be added to the set.  The actual sover just keeps using these
two functions until it runs out of work to do.
Note that we start by first adding all assumptions, and only then we consider
the goals because the assumptions might help us to solve the goals.
-------------------------------------------------------------------------------}

addWorkItems :: PropSet -> InertSet -> Maybe InertSet
addWorkItems ps is =
 case getProp (given ps) of
   Just (g,gs) ->
     do r <- addGiven g is
        let js = mkInert insertGiven r
        addWorkItems (unionPropSets (newWork r) ps { given = gs }) js

   Nothing ->
     case getProp (wanted ps) of
       Just (w,ws) ->
         do r <- addWanted w is
            let js = mkInert insertWanted r
            addWorkItems (unionPropSets (newWork r) ps { wanted = ws }) js
       Nothing -> return is

  where
  addIfAny _ Nothing js     = js
  addIfAny add (Just i) js  = add i js

  mkInert add r = addIfAny add (whatNext r) $ case newInert r of
                                                Nothing -> is
                                                Just js -> js


--------------------------------------------------------------------------------
#else
--------------------------------------------------------------------------------

{- Inetrface with GHC's solver -}

data NumericsResult = NumericsResult
  { numNewWork :: WorkList
  , numInert   :: Maybe CanonicalCts   -- Nothing for "no change"
  , numNext    :: Maybe CanonicalCt
  }


-- We keep the original type in numeric constants to preserve type synonyms.
toTerm :: Xi -> Term
toTerm xi = case mplus (isNumberTy xi) (isNumberTy =<< tcView xi) of
              Just n -> Num n (Just xi)
              _      -> Var xi

fromTerm :: Term -> Xi
fromTerm (Num n mb) = fromMaybe (mkNumberTy n) mb
fromTerm (Var xi)   = xi

toProp :: CanonicalCt -> Prop
toProp (CDictCan { cc_class = c, cc_tyargs = xis })
  | className c == lessThanEqualClassName = Prop Leq (map toTerm xis)

toProp (CFunEqCan { cc_fun = tc, cc_tyargs = xis, cc_rhs = xi2 })
  | tyConName tc == addTyFamName = Prop Add (ts ++ [t])
  | tyConName tc == mulTyFamName = Prop Mul (ts ++ [t])
  | tyConName tc == expTyFamName = Prop Exp (ts ++ [t])

    where ts = map toTerm xis
          t  = toTerm xi2

toProp p = panic $
  "[TcTypeNats.toProp] Unexpected CanonicalCt: " ++ showSDoc (ppr p)

{- XXX: Todo
canonicalNum :: CanonicalCts -> CanonicalCts -> CanonicalCts -> CanonicalCt ->
                TcS NumericsResult
canonicalNum given derived wanted prop =
  case cc_flavor prop of
    Wanted {}   -> solveNumWanted given derived wanted prop
    Derived {}  -> addNumDerived  given derived wanted prop
    Given {}    -> addNumGiven    given derived wanted prop

{- Disables the solver.
  return NumericsResult { numInert    = Nothing
                        , numNewWork  = emptyWorkList
                        , numNext     = Just prop
                        }
-}
-}

#endif

{-------------------------------------------------------------------------------
Functions on natural numbers.
-------------------------------------------------------------------------------}

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


{-------------------------------------------------------------------------------
Misc.
-------------------------------------------------------------------------------}

-- | Choce an element from a list in all possible ways.
choose :: [a] -> [(a,[a])]
choose []     = []
choose (x:xs) = (x,xs) : [ (y, x:ys) | (y,ys) <- choose xs ]

-- | For debuging lists of things.
tr :: Show a => String -> [a] -> b -> b
tr x ys z = trace x (trace msg z)
  where msg = case ys of
                [] -> "  (empty)"
                _  -> unlines [ "  " ++ show y | y <- ys ]



#include "TcTypeNatsRules.hs"


