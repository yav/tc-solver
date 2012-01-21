Notes on Solving Constraints
============================

This document outlines the ideas behind the implementation of the...


The Basic Problem
-----------------

We need to check the validity of problems of the form `Gs => Ws` where `Gs` and
`Ws` are both conjunctions of quantifier-free atoms.  The assumptions, `Gs`,
(called _givens_ in GHC) usually arise from explicit annotations in the source
code, while the conclusions, `Ws`, (called _wanteds_ in GHC) correspond to
constraints that were inferred by the compiler while it was analyzing the
source code.  The purpose of the constraint solver is to find a way to satisfy
the inferred constraints in terms of the ones that are available.

For example, the following Haskell constructs may provide assumptions (givens):

  * explicit type signatures,
  * the context of conditional instance declarations,
  * pattern matching on values with existentially quantified components,
  * pattern matching on values that belong to a GADT.

There are two main situations that give rise to new goals (wanteds):

  * When checking that two types are equal, and
  * when using polymorphic values with qualified types: we have to
    solve the constraints on the qualified type, to ensure that the
    specific instantiation is valid.



First-Order Logic (FOL)
-----------------------

We are working in the following fragment of first-order logic:

    data Term     = Con ConSym [Term]     -- (i.e., type)
                  | Var Var

    data Atom     = Atom PredSym [Term]   -- (i.e., constraint)

    data Formula  = And [Atom]
                  | Implies [Atom] [Atom]

There are no quantifiers because we have no language constructs that
introduce locally quantified constraints.  Because the formulas contain
no quantifiers, any variables that appear in terms are going to be free.
For the purposes of solving, such variables are treated as constant
symbols of arity 0.

To make matters more concrete, the solver for type-level naturals
uses the following constant and predicate symbols:

    data ConSym
      = Num Integer -- literal    :: Nat

    data PredSym
      = Eq   -- equality          :: Nat -> Nat        -> Constraint
      | Leq  -- ordering          :: Nat -> Nat        -> Constraint
      | Add  -- addition          :: Nat -> Nat -> Nat -> Constraint
      | Mul  -- multiplication    :: Nat -> Nat -> Nat -> Constraint
      | Exp  -- exponentiation    :: Nat -> Nat -> Nat -> Constraint

The (binary) operations for addition, multiplication, and exponentiation
are presented in (ternary) predicate form, so `Add x y z` corresponds to
the equation `(x + y) ~ z`.  This fragment of first-oder logic is
undecidable so some valid programs will---inevitably---be rejected.
Note that because the only constant symbols in this theory are the
literals, our terms have no interesting structure: a term is either
a literal or a variable.


Validity and Satisfiability in FOL
----------------------------------

Assuming a particular interpretation of the predicate and constant
symbols of a theory, we can ask if some formula holds in the theory.
When the formula contains no free variables, this is a yes/no question.
For example, this is how we can compute if a variable-free formula holds
with the usual interpretation of the theory of natural numbers:

    evalTerm (Con (Num x) [])  = x

    evalAtom (Atom p xs) =
      case (p, map evalTerm xs) of
        (Eq,  [x,y])   -> x == y
        (Leq, [x,y])   -> x <= y
        (Add, [x,y,z]) -> x + y == z
        (Mul, [x,y,z)  -> x * y == z
        (Exp, [x,y,z]) -> x ^ y == z

    evalFormula f =
      case f of
        And as        -> evalAtoms as
        Implies as bs -> evalAtoms bs || not (evalAtoms as)

      where evalAtoms cs = and (map evalAtom cs)


However, if a formula has free variables, then the answer might depend
on the values of those variables.  A _variable assignment_ is a
substitution, which assigns a concrete (i.e., variable-free) term to a
set of variables.

  * A formula is _satisfiable_ if there is a variable assignment that
    makes it true, otherwise it is _unsatisfiable_.

  * A formula is _valid_ if it is true for any variable assignment.

So, when we are asked if a formula with free variables holds, we can
answer in three different ways:

  * yes,   meaning that the formula is valid,
  * no,    meaning that the formula is unsatisfiable, and
  * maybe, meaning that the truth of the formula depends on the free
           variables (i.e., we know of two assignments: one that makes
           the formula true, and one that makes it false).

Note that, in general, if we have a way to determine if a formula is
satisfiable or not, then we can determine its validity by checking if
the formula's negation is satisfiable.


An Additioanl Problem: Simplification
-------------------------------------

Consider the formula:

    (5 + 3 = 8, x <= y, x <= y, y <= z, x <= z)

This formula is neither valid nor unsatisfiable so we can't outright accept
or reject the program that gave rise to it.  Instead, we have to propagate
the formula as an additional constraint.  While it would not be incorrect
to propagate the formula as it is, it is better if we first simplified it
the equivalent but more readable version:

    (x <= y, y <= z)


(x * y1 = z, x * y2 = z, 1 <= x)

-->

(x * y1 = z, 1 <= x, y2 ~ y1)



(x * y1 = 5, x * y2 = 5, 1 <= x)

-->

(x * y1 = 5, y2 ~ y1)





An Additional Probem: Improvement
---------------------------------

Consider the formula `(5 + 3) ~ x` (i.e., we have a single "wanted" and no
"givens").  It belongs to the "maybe" section described in the previous
section: we can't say that it is true (valid) because it does not hold
when `x ~ 9`; we also can't say that it is false (unsatisfiable), because
it does hold when `x ~ 8`.












Decision Procedures
-------------------

A decision procedure is an algorithm that can determine if a formula is
true in a finite (but not necessarily short!) amount of time.  If we are
working with an undecidable theory, then it is also possible that the
algorithm returns a fourth answer: "I don't know", meaning that
we could not determine the answer.

Note about Haskell and open theories (adding instances changes the
theory), so we are working with a family of decision procedures.

Alternatively all have to allow quantifiers in givens...




