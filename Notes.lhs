\documentclass{article}

\usepackage{fancyvrb}
\DefineVerbatimEnvironment{code}{Verbatim}{fontsize=\small}
\DefineVerbatimEnvironment{example}{Verbatim}{fontsize=\small}

\newcommand{\To}{\Rightarrow}


\begin{document}

\begin{code}
module Notes where

import Control.Monad(mzero,foldM,guard)
import Test
import Data.List(find,nub)
import Debug.Trace

\end{code}


\subsection{The Inert Set}

The {\em inert set} keeps track of the facts known by the solver
and the goals that we tried to solve but failed.

\begin{code}
data InertSet = InertSet { given :: [Prop], wanted :: [Prop] }

emptyInertSet :: InertSet
emptyInertSet = InertSet { given = [], wanted = [] }
\end{code}

This data-structure satisfies the invariant that the stored propositions
cannot ``interact''.  Like this:

\begin{code}
inert_prop :: InertSet -> Bool
inert_prop props = all (isNotForAll . uncurry entails) $
  [ (ws ++ given props, w) | (w,ws) <- choose (wanted props) ] ++
  [ (gs, g)                | (g,gs) <- choose (given props)  ]
\end{code}


\subsection{WorkItems}

\begin{code}
type WorkItem         = (PropKind,Prop)
data PropKind         = Given | Wanted
                        deriving Show

addInert :: WorkItem -> InertSet -> InertSet
addInert (Given, g)  is = is { given  = g : given is }
addInert (Wanted, w) is = is { wanted = w : wanted is }
\end{code}





A central component of the solver is the entailment function.

As the name suggests, it tells us if a set of assumptions
(the first argument), entail a certain proposition (the second argument).
The function returns one of the following answers:

\begin{code}
data Answer = NotForAny | NotForAll | YesIf [Prop]

\end{code}

Informally, the three values may be thought of as ``certainly not'',
''not in its current form'', and ''(a qualified) yes''.  More precisely,
\Verb"NotForAny" states that the proposition in question contradicts the
given set of assumptions, no matter how we instantiate it.  For example,
the proposition $2 + 3 = 6$ will result in \Verb"NotForAny", no matter
what the set of assumptions.
$$
\forall x.~not~(P~x)
$$

A milder form of rejection is captured by \Verb"NotForAll"---in this
case we cannot
$$
not~(\forall x.~P~x)
$$

$$
\forall x.~Q~x \To P~x
$$





\subsection{Interface to The Combined Solver}

\begin{code}
data PassResult = PassResult
  { inertChanges  :: InertSetChanges
  , newWork       :: [WorkItem]
  , consumed      :: Bool
  }

data InertSetChanges  = NoChanges | NewInertSet InertSet

updateInerts :: InertSetChanges -> InertSet -> InertSet
updateInerts NoChanges is       = is
updateInerts (NewInertSet is) _ = is
\end{code}



\subsection{A Solver}

\begin{code}
addWorkItems :: [WorkItem] -> InertSet -> Maybe InertSet
addWorkItems [] is = return is
addWorkItems (wi : wis) is =
  do r <- addWork is wi
     let is1 = updateInerts (inertChanges r) is
     addWorkItems (newWork r ++ wis)
                  (if consumed r then is1 else addInert wi is1)
\end{code}




\begin{code}
addWork :: InertSet -> WorkItem -> Maybe PassResult
addWork is (Given,p)  = addGiven is p
addWork is (Wanted,p) = addWanted is p

addGiven :: InertSet -> Prop -> Maybe PassResult
addGiven props g =
  case entails (given props) g of

    NotForAny -> mzero

    NotForAll -> return
      PassResult
        { inertChanges  = NewInertSet props { wanted = [] }
        , newWork       = [ (Wanted,w) | w <- wanted props ]
        , consumed      = False
        }

    YesIf ps -> return
      PassResult
        { inertChanges    = NoChanges
        , newWork         = [ (Given,p) | p <- ps ]
        , consumed        = True
        }
\end{code}


\begin{code}
addWanted :: InertSet -> Prop -> Maybe PassResult
addWanted props w =
  case entails (wanted props ++ given props) w of

    NotForAny -> mzero

    YesIf ps -> return
      PassResult
        { inertChanges    = NoChanges
        , newWork         = [ (Wanted,p) | p <- ps ]
        , consumed        = True
        }

    NotForAll ->
      do (inert,restart,changes) <-
           foldM check ([],[],False) (choose (wanted props))
         if changes
          then return PassResult
                 { inertChanges = NewInertSet props { wanted = inert }
                 , newWork      = [ (Wanted,p) | p <- restart ]
                 , consumed     = False
                 }
          else return PassResult
                 { inertChanges = NoChanges
                 , newWork      = []
                 , consumed     = False
                 }

  where
  check (inert,restart,changes) (w1,ws) =
    case entails (w : ws ++ given props) w1 of
      NotForAny -> mzero
      NotForAll -> return (w1 : inert, restart,changes)
      YesIf ps  -> return (inert, ps ++ restart,True)
\end{code}


Note that it is important that when the solver answers \Verb"YesIf",
the sub-goals should be simpler than the original in some way.  This
avoids non-terminating loops of the following form:

\begin{example}
entails [p] q   = NotForAll
entails [q] p   = YesIf [p1]
entails [q] p1  = NotForAll
entails [p1] q  = YesIf [q1]
etc.
\end{example}




\subsection{Improvement}

Consider a goal like $5 + 3 = x$.  We cannot solve it directly
because we don't know the value of $x$.  However, by using forward
reasoning we know that this goal implies the fact $x = 8$.
Furthermore, this facts can be used to solve the original goal, so it is
logically equivalent to it.  Therefore, we can discharge the original
goal, and start looking for a solution to the simpler goal $x = 8$.

We prefer goals that are simple equalities because they can be used
by other parts of the system too.  This is the basic idea behind
computing an "improving substitution", we consider only the
implied equalities.

Essentially, what we are doing is identifying a logical equivalence
between that wanted goal and another (presumably "better" set of
predicates).  The two are equivalent because we know that "w" entails
the "is" (guaranteed by the "implies" function, see "sound1" above),
and also we have checked that the "is" entail "w".

The remaining thing is to ensure that the new equivalent set of goals
is indeed somehow "better" than the original goal.  This is the
case if we restrict ourselves to just improving substitutions
(equalities are always better then non-equalities because all theories
understand them, and also they make a more specialized instance
of the original goal).

Here is an example of why it is important that the new set is "better":
Add new wanted "x + y = z".
This is not entailed on its own.
It implies "y + x = z".
This can be used to discharge the original goal "x + y = z".
Now we have a new wanted goal "y + x = z".
And we can keep going like this, looping forever.


\subsection{Substitutions}

\begin{code}
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
  apSubst su (EqFun op x y z) = EqFun op (apSubst su x)
                                             (apSubst su y)
                                             (apSubst su z)
  apSubst su (Eq x y)         = Eq (apSubst su x) (apSubst su y)
  apSubst su (Leq x y)        = Leq (apSubst su x) (apSubst su y)

substToEqns :: Subst -> [Prop]
substToEqns su = [ Eq (Var x) t | (x,t) <- su ]

-- Turn the equations that we have into a substitution, and return
-- the remaining proposition.
improvingSubst :: [Prop] -> Maybe (Subst, [Prop])
improvingSubst ps0 = do (su,ps) <- loop ([],[]) ps0
                        return (su, filter (not . trivial) ps)
  where
  loop (su,rest) (Eq x y : es) =
    do su1 <- mgu x y
       loop (compose su1 su, apSubst su1 rest) (apSubst su1 es)
  loop (su,rest) (e : es) = loop (su,e:rest) es
  loop su [] = return su
\end{code}




If we have $p : x = t$ as an assumption,
then we replace occurances of $x$ with $t$.
To adjust the proofs of assumptions we use congruence.
Similarly, we can adjust goals to remove $x$, solving the original
goals with $x$ in terms of the new goals without $x$ and $p$.

\begin{example}
Prop
new_goal: FunEq op t y z
old-goal: FunEq op x y z
old_goal = CongFunEq op p refl refl new_goal


old_asmp: FunEq op x y z
new_asmp: FunEq op t x yz
new_asmp = CongFunEq op p refl refl old_asmp


\end{example}



Adding more assumptions cannot make things less contradictory
\begin{code}
entails_any_prop :: [Prop] -> Prop -> Prop -> Bool
entails_any_prop ps q p =
  case entails ps q of
    NotForAny -> isNotForAny (entails (p:ps) q)
    _         -> True
\end{code}

Droppoing assumptions cannot make things more contradictory or more
defined.
\begin{code}
enatils_all_prop :: Prop -> [Prop] -> Prop -> Bool
enatils_all_prop p ps q =
  case entails (p:ps) q of
    NotForAll -> isNotForAll (entails ps q)
    _         -> True
\end{code}


\begin{code}
entails :: [Prop] -> Prop -> Answer
entails ps p | tr "entails?:" ps
             $ trace "  --------"
             $ trace ("  " ++ show p) False = undefined
entails ps' p' =
  case closure ps' of
    Nothing -> error "bug: Inert invariant failed!"
    Just (su,ps) ->
      let p = apSubst su p'
      in if solve ps p
           then trace "yes!" $ YesIf []
           else trace "try improvement" $
                case closure (p:ps) of
                  Nothing -> trace "definately not" NotForAny
                  Just (su1,_)
                    | solve (apSubst su1 ps) (apSubst su1 p) ->
                        trace "yes!" YesIf (substToEqns su1)
                    | otherwise -> trace "no" NotForAll



closure :: [Prop] -> Maybe (Subst, [Prop])
closure ps = closure1 =<< improvingSubst ps

closure1 :: (Subst, [Prop]) -> Maybe (Subst, [Prop])
closure1 (su0, ps0) =
  do (su, ps) <- improvingSubst
              $ do (q,qs) <- choose ps0
                   i      <- implied qs q
                   guard (not (elem i ps0))
                   return i

     let su1 = compose su su0
         ps1 = apSubst su ps0

     case ps of
       [] -> tr "computed closure:" ps1
           $ return (su1, ps1)
       _  -> tr "adding:" ps $ closure1 (su1,nub (ps ++ ps1))


tr :: Show a => String -> [a] -> b -> b
tr x ys z = trace x (trace msg z)
  where msg = case ys of
                [] -> "  (empty)"
                _  -> unlines [ "  " ++ show y | y <- ys ]
\end{code}


\begin{code}
trivial :: Prop -> Bool
trivial = solve []
\end{code}

\begin{code}
solve :: [Prop] -> Prop -> Bool
solve asmps prop =
      solve0 [] prop
   || any (`solve1` prop) p1
   || any (`solve2` prop) p2
   || any (`solve3` prop) p3
   -- || any (`solve4` prop) p4

  where
  p1 : p2 : p3 : p4 : p5 : _ = map (`nth_product` asmps) [ 1 .. ]


implied :: [Prop] -> Prop -> [Prop]
implied asmps prop =
  frule0 [] prop ++
  concatMap (`frule1` prop) p1 ++
  concatMap (`frule2` prop) p2 {- ++
  concatMap (`frule3` prop) p3 ++
  concatMap (`frule4` prop) p4 ++
  concatMap (`frule5` prop) p5 -}
  where
  p1 : p2 : p3 : p4 : p5 : _ = map (`nth_product` asmps) [ 1 .. ]




\end{code}



\begin{code}
test :: [WorkItem] -> Maybe InertSet
test ps = addWorkItems ps emptyInertSet

\end{code}

\begin{code}
instance Show InertSet where
  show is = "\n" ++
            unlines [ "G: " ++ show p | p <- given is ] ++
            unlines [ "W: " ++ show p | p <- wanted is ]


choose :: [a] -> [(a,[a])]
choose []     = []
choose (x:xs) = (x,xs) : [ (y, x:ys) | (y,ys) <- choose xs ]

nth_product :: Int -> [a] -> [[a]]
nth_product n xs | n <= 1     = do x <- xs
                                   return [x]
                 | otherwise  = do (x,ys) <- choose xs
                                   zs <- nth_product (n-1) ys
                                   return (x : zs)

isNotForAny :: Answer -> Bool
isNotForAny NotForAny = True
isNotForAny _         = False


isNotForAll :: Answer -> Bool
isNotForAll NotForAll = True
isNotForAll _         = False

isYesIf :: Answer -> Bool
isYesIf (YesIf _)     = True
isYesIf _             = False

\end{code}
\end{document}

