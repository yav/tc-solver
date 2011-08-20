\documentclass{article}

\usepackage{fancyvrb}
\DefineVerbatimEnvironment{code}{Verbatim}{fontsize=\small}
\DefineVerbatimEnvironment{example}{Verbatim}{fontsize=\small}

\usepackage{amsmath}

\newcommand{\To}{\Rightarrow}
\newcommand{\ent}{\vdash}


\begin{document}


This document is a literate Haskell file.

\begin{code}
module Notes where

import Control.Monad(mzero,foldM,guard)
import Test
import Data.List(find,nub)
import Debug.Trace
\end{code}



\subsection{Sets of Propositions}

The solver manipulates two kinds of propositions: {\em given} propositions
correspond to assumptions that may be used without proof,
while {\em wanted} propositions correspond to goals that need to be proved.
When working with collections of properties, it is convenient to group
the assumptions and goals separately:

\begin{code}
data PropSet = PropSet { given :: [Prop], wanted :: [Prop] }

emptyPropSet :: PropSet
emptyPropSet = PropSet { given = [], wanted = [] }

insertGiven :: Prop -> PropSet -> PropSet
insertGiven g ps = ps { given = g : given ps }

insertWanted :: Prop -> PropSet -> PropSet
insertWanted w ps = ps { wanted = w : wanted ps }

unionPropSets :: PropSet -> PropSet -> PropSet
unionPropSets ps1 ps2 = PropSet { given  = given ps1  ++ given ps2
                             , wanted = wanted ps1 ++ wanted ps2
                             }
\end{code}


\subsection{Entailment}

A central component of the solver is the entailment function, which determines
if a set of assumptions (the first argument), entail a certain proposition
(the second argument).

\begin{code}
entails :: [Prop] -> Prop -> Answer
\end{code}

The entailment function may return one of three possible answers,
informally corresponding to ``certainly not'', ''not in its current form'',
and ''(a qualified) yes'':

\begin{code}
data Answer = NotForAny | NotForAll | YesIf [Prop]
\end{code}

More precisely, \Verb"NotForAny" asserts that the proposition in question
contradicts the given set of assumptions, no matter how we instantiate its
free variables.  The following two examples both result in a
\Verb"NotForAny" answer (we use the more traditional mathematical notation
for entailment)
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
This results in \Verb"NotForAll" because without any assumptions the
equation does not hold.  However some instantiations (e.g., $x = 2, y = 4$)
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
Section~\ref{sec_improvement}.



\subsection{The Inert Set}

The {\em inert set} is a collection of propositions, which keeps track
of the facts that are known by the solver, as well as any goals that
were attempted but not solved.  We refer to this set as ``inert'' because
the propositions in it cannot ``interact'' with each other.  To distinguish
sets with this property from other sets of propositions we use a separate
type synonym:

\begin{code}
type InertSet = PropSet
\end{code}

More formally, the following predicate captures the ``non-interacion''
invariant of the inert set:

\begin{code}
inert_prop :: InertSet -> Bool
inert_prop props = all (isNotForAll . uncurry entails) $
  [ (gs, g)                | (g,gs) <- choose (given props)  ] ++
  [ (ws ++ given props, w) | (w,ws) <- choose (wanted props) ]
\end{code}

The predicate consists of two parts, both of the same form:  the first one
asserts that the collection of given facts is consistent and non-redundant,
while the second asserts the same property for the set of goals.
The ``consistent and non-redundant'' property is captured
by the requirement that when we use the entailment function we get
the answer \Verb"NotForAll"---had we obtained \Verb"NotFroAny", we would
have a constradiction and hence the propositions would not be consistent,
and if we ontained \Verb"YesIf", then then the proposition would
be redundant and hence may be eliminated.  The predicate makes use
of the auxiliary function \Verb"choose", which extracts a single
element from a list in all possible ways:

\begin{code}
choose :: [a] -> [(a,[a])]
choose []     = []
choose (x:xs) = (x,xs) : [ (y, x:ys) | (y,ys) <- choose xs ]
\end{code}





\subsection{The Solver}

The purpose of the solver is to turn an arbitrary set of propositions
into an inert one.  This is done by starting with some inert set
(e.g., the empty set of propositions) and then adding each new proposition
one at a time.  Assumptions and goals are added in different ways, so
we have two different functions to add a proposition to an existing
inert set:

\begin{code}
addGiven  :: Prop -> InertSet -> Maybe PassResult
addWanted :: Prop -> InertSet -> Maybe PassResult

data PassResult = PassResult { newInert :: InertSet, newWork :: PropSet }
\end{code}

If successful, both functions return a \Verb"PassResult" value, which
contains an updated inert set and, potentially, some additional propositions
that need to be added to the set.  The actual sover just keeps using these
two functions until it runs out of work to do:

\begin{code}
addWorkItems :: PropSet -> InertSet -> Maybe InertSet
addWorkItems ps is =
 case given ps of
   g : gs ->
     do r <- addGiven g is
        addWorkItems (unionPropSets (newWork r) ps { given = gs }) (newInert r)

   [] ->
     case wanted ps of
       w : ws ->
         do r <- addWanted w is
            addWorkItems (unionPropSets (newWork r) ps { wanted = ws })
                                                                  (newInert r)
       [] -> return is
\end{code}

Note that we start by first adding all assumptions, and only then we consider
the goals because the assumptions might help us to solve the goals.


\subsection{Adding a New Assumption}

\begin{code}
addGiven g props =
  case entails (given props) g of

    NotForAny -> mzero

    NotForAll -> return
      PassResult
        { newInert  = PropSet { wanted = [], given = g : given props }
        , newWork   = props { given = [] }
        }

    YesIf ps -> return
      PassResult
        { newInert  = props
        , newWork   = emptyPropSet { given = ps }
        }
\end{code}


\subsection{Adding a New Goal}

\begin{code}
addWanted w props =
  case entails (wanted props ++ given props) w of

    NotForAny -> mzero

    YesIf ps -> return
      PassResult
        { newInert  = props
        , newWork   = emptyPropSet { wanted = ps }
        }

    NotForAll ->
      do (inert,restart,changes) <-
           foldM check ([],[],False) (choose (wanted props))

         if changes
           then return PassResult
                  { newInert = props { wanted = w : inert }
                  , newWork  = emptyPropSet { wanted = restart }
                  }
           else return PassResult
                  { newInert = props { wanted = w : wanted props }
                  , newWork  = emptyPropSet
                  }

  where
  check (inert,restart,changes) (w1,ws) =
    case entails (w : ws ++ given props) w1 of
      NotForAny -> mzero
      NotForAll -> return (w1 : inert, restart, changes)
      YesIf ps  -> return (inert, ps ++ restart, True)
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
-- the remaining propositions.
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

Dropping assumptions cannot make things more contradictory or more
defined.
\begin{code}
enatils_all_prop :: Prop -> [Prop] -> Prop -> Bool
enatils_all_prop p ps q =
  case entails (p:ps) q of
    NotForAll -> isNotForAll (entails ps q)
    _         -> True
\end{code}


\begin{code}
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
                    | solve (apSubst su1 ps) (apSubst su1 p)
                   && not (p' `elem` eqns) ->
                        trace "yes!" YesIf eqns
                    | otherwise -> trace "no" NotForAll
                    where eqns = substToEqns su1



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
       _  -> tr "adding:" (nub ps) $ closure1 (su1,nub (ps ++ ps1))


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
solve  _ (Eq x y) | x == y = True
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
instance Show PropSet where
  show is = "\n" ++
            unlines [ "G: " ++ show p | p <- given is ] ++
            unlines [ "W: " ++ show p | p <- wanted is ]


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

