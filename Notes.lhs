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
import Debug.Trace
\end{code}



\subsection{Sets of Propositions}

The solver manipulates two kinds of propositions: {\em given} propositions
correspond to assumptions that may be used without proof,
while {\em wanted} propositions correspond to goals that need to be proved.
When working with collections of properties, it is convenient to group
the assumptions and goals separately:

\begin{code}
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
\end{code}


\subsection{Entailment}

A central component of the solver is the entailment function, which determines
if a set of assumptions (the first argument), entail a certain proposition
(the second argument).

\begin{code}
entails :: Props -> Prop -> Answer
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
  [ (gs, g)                          | (g,gs) <- chooseProp (given props) ] ++
  [ (unionProps ws (given props), w) | (w,ws) <- chooseProp (wanted props) ]
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
element from a list in all possible ways.






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
 case getProp (given ps) of
   Just (g,gs) ->
     do r <- addGiven g is
        addWorkItems (unionPropSets (newWork r) ps { given = gs }) (newInert r)

   Nothing ->
     case getProp (wanted ps) of
       Just (w,ws) ->
         do r <- addWanted w is
            addWorkItems (unionPropSets (newWork r) ps { wanted = ws })
                                                                  (newInert r)
       Nothing -> return is
\end{code}

Note that we start by first adding all assumptions, and only then we consider
the goals because the assumptions might help us to solve the goals.


\subsection{Adding a New Assumption}

\begin{code}
addGiven g props =
  case entails (given props) g of

    NotForAny -> mzero

    NotForAll -> return PassResult
      { newInert  = PropSet { wanted = noProps
                            , given = addProp g (given props)
                            }
      , newWork   = props { given = noProps }
      }

    YesIf ps -> return PassResult
      { newInert  = props
      , newWork   = emptyPropSet { given = propsList ps }
      }
\end{code}


\subsection{Adding a New Goal}

\begin{code}
addWanted w props =
  case entails (unionProps (wanted props) (given props)) w of

    NotForAny -> mzero

    YesIf ps -> return PassResult
      { newInert  = props
      , newWork   = emptyPropSet { wanted = propsList ps }
      }

    NotForAll ->
      do let start = (addProp w noProps, noProps)
         (inert,restart) <- foldM check start (chooseProp (wanted props))

         return PassResult
           { newInert = props { wanted = inert }
           , newWork  = emptyPropSet { wanted = restart }
           }

  where
  check (inert,restart) (w1,ws) =
    case entails (addProp w (unionProps ws (given props))) w1 of
      NotForAny -> mzero
      NotForAll -> return (addProp w1 inert, restart)
      YesIf ps  -> return (inert, foldr addProp restart ps)
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
substToEqns :: Subst -> [Prop]
substToEqns su = [ Prop Eq [Var x, t] | (x,t) <- su ]

-- Turn the equations that we have into a substitution, and return
-- the remaining propositions.
improvingSubst :: Props -> Maybe (Subst, Props)
improvingSubst ps  = do su <- loop [] (getPropsFor Eq ps)
                        return (su, filterProp (not . trivial)
                                   $ apSubst su $ rmProps Eq ps)
  where
  loop su ([x,y] : eqs) =
    do su1 <- mgu x y
       loop (compose su1 su) (apSubst su1 eqs)
  loop _ (_ : _) = error "bug: improveSubst eqn of arity not 2"
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
entails_any_prop :: Props -> Prop -> Prop -> Bool
entails_any_prop ps q p =
  case entails ps q of
    NotForAny -> isNotForAny (entails (addProp p ps) q)
    _         -> True
\end{code}

Dropping assumptions cannot make things more contradictory or more
defined.
\begin{code}
enatils_all_prop :: Prop -> Props -> Prop -> Bool
enatils_all_prop p ps q =
  case entails (addProp p ps) q of
    NotForAll -> isNotForAll (entails ps q)
    _         -> True
\end{code}

\begin{code}
{-
extend0 prop =
  case prop of
    EqFun Add x y z           -> return [ Leq x z, Leq y z, EqFun Add y x z ]
    EqFun Mul x y z
      | Num m _ <- x, 1 <= m  -> return [ Leq y z, EqFun Mul y x z ]
      | otherwise             -> return [ EqFun Mul y x z ]
    EqFun Exp x y z
      | Num m _ <- x, 2 <= m  -> return [ Leq y z ]
      | Num m _ <- y, 1 <= m  -> return [ Leq x z ]
    _                         -> return []


extend1 :: Prop -> Prop -> Maybe [Prop]
extend1 asmp prop =
  case prop of

    Leq x y
      | Leq a (Num m _) <- prop, Num n _ <- x, m <= n -> return [ Leq a y ]
      | Leq (Num m _) a <- prop, Num n _ <- y, n <= m -> return [ Leq y a ]
      | Leq y' z        <- prop, y == y'              -> return [ Leq x z ]
      | Leq a x'        <- prop, x == x'              -> return [ Leq a y ]
      | Leq y' x'       <- prop, x == x', y == y'     -> return [ Eq x y ]

    EqFun Add x y z
      | EqFun Add x' y' z' <- prop, x == x', y == y'  -> return [ Eq z z' ]
      | EqFun Add x' y' z' <- prop, x == x', z == z'  -> return [ Eq y y' ]
      | EqFun Add x' y' z' <- prop, y == y', z == z'  -> return [ Eq x x' ]

    EqFun Mul x y z
      | EqFun Mul x' y' z' <- prop, x == x', y == y'  -> return [ Eq z z' ]

    EqFun Mul (Num m _) y z
      | EqFun Mul (Num m' _) y' z' <- prop, 1 <= m, m == m', z == z'
                                                      -> return [ Eq y y' ]

    EqFun Exp x y z
      | EqFun Exp x' y' z' <- prop, x == x', y == y'  -> return [ Eq z z' ]

    EqFun Exp (Num m _) y z
      | EqFun Exp (Num m' _) y' z' <- prop, 2 <= m, m == m', z == z'
                                                      -> return [ Eq y y' ]
    EqFun Exp x (Num m _) z
      | EqFun Exp x' (Num m' _) z' <- prop, 1 <= m, m == m', z == z'
                                                      -> return [ Eq x x' ]

    -- 5 + x = y & 7 + x = z  --> 2 + y = z
    EqFun Add (Num m _) y z
      | EqFun Add (Num n _) y' z' <- prop, y == y' ->
        if m >= n then return [ EqFun Add (num (m - n)) z' z ]
                  else return [ EqFun Add (num (n - m)) z z' ]

    -- 5 + x = y & 7 + y = z   --> 13 + x = z
    EqFun Add (Num m _) x y
      | EqFun Add (Num n _) y' z <- prop, y == y' ->
                                        return [ EqFun Add (num (m + n)) x z ]

    EqFun Add (Num n _) y' z
      | EqFun Add (Num m _) x y <- prop, y == y' ->
                                        return [ EqFun Add (num (m + n)) x z ]

{-
    EqFun Add x y (Num m _)
      | EqFun Add x' y' (Num n _)


    -- x + y = 5, x + y' = 7 --> y + 2 = y'

    -- x + y + 2 = x + y'
-}
    _ -> return []
-}


\end{code}

\begin{code}
entails ps p | tr "entails?:" (propsToList ps)
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
                 case closure (addProp p ps) of
                   Nothing -> trace "definately not" NotForAny
                   Just (su1,_)
                     | solve (apSubst su1 ps) (apSubst su1 p)
                    && not (p' `elem` eqns) ->
                         trace "yes!" YesIf eqns
                     | p == p'   -> trace "no" NotForAll
                     | otherwise -> YesIf [p]
                     where eqns = substToEqns su1



closure :: Props -> Maybe (Subst, Props)
closure ps = closure1 =<< improvingSubst ps

closure1 :: (Subst, Props) -> Maybe (Subst, Props)
closure1 (su0, ps0) =
  do (su, ps) <- improvingSubst
              $ propsList
              $ do (q,qs) <- chooseProp ps0
                   i      <- implied qs q
                   guard (not (elemProp i ps0))
                   return i

     let su1 = compose su su0
         ps1 = apSubst su ps0

     if isEmpty ps
       then tr "computed closure:" (propsToList ps1)
           $ return (su1, ps1)
       else tr "adding:" (propsToList ps) $ closure1 (su1, unionProps ps ps1)

\end{code}


\begin{code}
trivial :: Prop -> Bool
trivial = solve noProps

solve :: Props -> Prop -> Bool
solve  _ (Prop Eq [x,y]) | x == y = True
solve ps p = solve0 [] p || elemProp p ps
\end{code}



\begin{code}
instance Show PropSet where
  show is = "\n" ++
            unlines [ "G: " ++ show p | p <- propsToList (given is) ] ++
            unlines [ "W: " ++ show p | p <- propsToList (wanted is) ]


isNotForAny :: Answer -> Bool
isNotForAny NotForAny = True
isNotForAny _         = False

isNotForAll :: Answer -> Bool
isNotForAll NotForAll = True
isNotForAll _         = False

isYesIf :: Answer -> Bool
isYesIf (YesIf _)     = True
isYesIf _             = False


tr :: Show a => String -> [a] -> b -> b
tr x ys z = trace x (trace msg z)
  where msg = case ys of
                [] -> "  (empty)"
                _  -> unlines [ "  " ++ show y | y <- ys ]

\end{code}


\end{document}

