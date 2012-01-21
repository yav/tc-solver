Evidence Generated by the Solver
================================

The solver for the type naturals works with evidence in the folloing format:

    data Ev = EvVar EvVar
            | EvApp EvAxiom [Type] [Ev]

Variables in proofs serve a dual purpose:

  * if a variable is bound, then the variable refers to a named sub-proof,
  * if a variable is unbound, then it indicates the use of an assumption.

Evidence application indicates the use of an axiom.  Axioms are of the form:

    forall as. (P1,P2,..,Pn) => Q

The parameters in an evidence application indicate how to instantiate
the quantified variables of the axiom, and provide proofs for its assumptions.

The solver for the type naturals uses quite a few axioms, corresponding to
the various rules that in knows about.  To make things concrete, here are
a few of them:

    data EvAxiom
    
      -- Basic equality
      = EqRefl      -- forall a.                        a ~ a
      | EqSym       -- forall a b.   (a ~ b)         => b ~ a
      | EqTrans     -- forall a b c. (a ~ b, b ~ c)  => a ~ c
      | Cong Pred   -- forall as bs. (as ~ bs, P as) => P bs
                    -- ("as" and "bs" refer to multiple variables)
    
      -- Basic order
      | LeqRefl     -- forall a.                         a <= a
      | LeqAsym     -- forall a b.   (a <= b, b <= a) => a ~ b
      | LeqTrans    -- forall a b c. (a <= b, b <= c) => a <= c
      | Leq0        -- forall a.                         0 <= a
    
      -- Definitions for concrete constants
      | DefAdd Integer Integer Integer  -- only if x + y = z
      | DefMul Integer Integer Integer  -- only if x * y = z
      | DefExp Integer Integer Integer  -- only if x ^ y = z
      | DefLeq Integer Integer          -- only if x <= y
    
      -- Various functional dependecies
      | FunAdd   -- forall a b c1 c2. ( a + b ~ c1
                                      , a + b ~ c2 )  => c1 ~ c2
    
      | SubL     -- forall a b1 b2 c. ( a + b1 ~ c
                                      , a + b2 ~ c )  => b1 ~ b2
    
      | SubR     -- forall a1 a2 b c. ( a1 + b ~ c
                                      , a2 + b ~ c )  => a1 ~ a2
    
      | FunMul   -- forall a b c1 c2. ( a * b ~ c1
                                      , a * b ~ c2 )  => c1 ~ c2
    
      | DivL     -- forall a b1 b2 c. ( 1 <= a,
                                      , a * b1 ~ c
                                      , a * b2 ~ c )  => b1 ~ b2
    
      | DivR     -- forall a1 a2 b c. ( 1 <= b
                                      , a1 * b ~ c
                                      , a2 * b ~ c )  => a1 ~ a2
    
      | FunExp   -- forall a b c1 c2. ( a ^ b ~ c1
                                      , a ^ b ~ c2 )  => c1 ~ c2
    
      | Log      -- forall a b1 b2 c. ( 2 <= a
                                      , a ^ b1 ~ c
                                      , a ^ b2 ~ c )  => b1 ~ b2
    
      | Root     -- forall a1 a2 b c. ( 1 <= b
                                      , a1 ^ b ~ c
                                      , a2 ^ b ~ c )  => a1 ~ a2
    
      -- etc..


Extending `Ev` to All of Haskell
================================

Despite the fact that I described `Ev` in the context of the solver for
type-level naturals, it can be used to represent all forms of evidence
in Haskell programs, just by extending the type for axioms.
The following sections show how that might work.  (For simplicity, in
the examples bellow I use a generic type `Name` to refer to everything;
in reality compilers tend to use many different flavors of name).


Instances
---------

A user-defined instance declaration corresponds to an axiom that allows us
to solve a certain form of predicate (the instance "head").  To support
this in `Ev` we would add a new axiom constructor:

    ...
    | Instance Name

When declaring instances programmers do not give them names, however
the compiler generates a unique name for each instance, so that it can
refer to it.  As an example, this would be the evidence for `Eq [Int]`:

    EvApp (Instance iEqList) [tInt] [EvApp iEqInt [] []]  -- Eq [Int]


Super Classes
-------------

Super-classes in a Haskell program also correspond to axioms, so we can
add support for them by adding new axiom of the form:

    ...
    | SuperClass Name Int   -- n'th super class

As an example, this is the super-class axiom for the `Ord` class:

    SuperClass cOrd 0       -- forall a. Ord a => Eq a

Thus, assuming that `p` is evidence for `Ord t`, we can construct
evidence for `Eq t` like this:

    EvApp (SuperClass cOrd 0) [t] [p]     -- Eq t

Note that, in general, the "super-classes" are arbitrary constraints:
they may be super-class constraints, equality predicates, or any other
predicate that we may add in the future.


Functional Dependencies
-----------------------

Just like super-classes, functional dependencies add extra axioms.
For example, consider the following class declaration:

    class Monad m => StateM m s | m -> s where ...

It results in two new axioms: one for the super-class and one for the
functional dependency:

    SuperClass cStateM 0 -- forall m s. StateM m s => Monad m
    FunDep     cStateM 0 -- forall m s1 s2. ( StateM m s1
                                            , StateM m s2 ) => s1 ~ s2

Thus, the representation can be extend to support functional dependencies
by adding a constrctor like this:

    ...
    | FunDep Name Int       -- n't functional dependency

So, assuming that `p` is evidence for `StateM m s1`, and `q` is evidence
for `StateM m s2`, then we can construct evidence for `s1 ~ s2` like this:

    EvApp (FunDep cStateM 0) [m,s1,s2] [p,q]  -- s1 ~ s2


Type Functions
--------------

Just like class instances correspond to axioms that define a class
predicate, type familiy instances correspond to axioms definig a type
funciton.  We can support them by extending the axiom type like this:

    ...
    | TyFun Name

As in the case for instaces, the compiler assigns a name to each
type familiy instance.  For example, consider the following declarations:

    type familiy Fun (a :: *) :: *
    type instance Fun [a] = Maybe a

They result in an axiom like this:

    TyFun tfFunList      --  forall a. Fun [a] ~ Maybe a

So, the evidence that `Fun [Int] ~ Maybe Int` looks as follows:

    EvApp (TyFun tfFunList) [Int] []    -- Fun [Int] ~ Maybe Int


Summary
-------

Here is what the type of combined type for evidence might look like:

    data Ev
      = EvVar EvVar
      | EvApp EvAxiom [Type] [Ev]

    data Axiom
      = Instance   Name
      | TyFun      Name
      | SuperClass Name Int
      | FunDep     Name Int
      | EqAxiom      EqAxiom
      | TypeNatAxiom TypeNatAxiom

    data EqAxiom
      = EqRefl | EqSym | ... etc.

    data TypeNatAxiom
      = FunAdd | SubL | ... etc.



