
Consider the associativity rule for addition:

    add_assoc     :: forall a b c. (a + b) + c ~ a + (b + c)

In its fully "canonicalized" form it becomes:

    add_assoc     :: forall a b c x y z1 z2.
      (a + b ~ x, b + c = y, x + c ~ z1, a + y ~ z2) => (z1 ~ z2)


Example:

    Goal: (a + b ~ x, x + c ~ z1, a + y = z1) => (b + c ~ y)


    F1: a + b ~ x
    F2: b + c ~ Y         -- name
    F3: x + c ~ z1
    F4: a + Y ~ Z         -- name
    F5: a + y ~ z1

    add_assoc F1 F2 F3 F4 :: z1 ~ Z

    F1:  a + b ~ x
    F2:  b + c ~ Y         -- name
    F3:  x + c ~ z1
    F4': a + Y ~ z1        -- "improve" with cong
    F5:  a + y ~ z1

    add_cancel_L F4' F5 :: Y ~ y

    F1:  a + b ~ x
    F2:  b + c ~ y         -- "improve" with cong
    F3:  x + c ~ z1
    F5:  a + y ~ z1

    goal is proved by F2.


Synthetic rules "package" this sort of reasoning for speaicl cases.
It'd be nice to avoid this special-casing. The question is how do we
know what to name.

Too much naming can lead to non-termination.  Example:
x + 1 ~ Y, Y + 1 ~ Y1, Y1 + 1 ~ Y2, etc...
The problem is that there are infinitely many things that can be named
but we need to narrow down the interesting ones.

In this example, the first nameing was motivated by the goal:
we'd like to know if `b + c = y`, well, let's say that `b + c = Y`
(which is OK because the functions are total), and see if we'll come
up with a proof that `Y ~ y`.

Why did we not choose `B + c = y`?  Because we don't know that such
a `B` exists (subtraction is not total in the naturals).

So, to show `P => a OP b ~ c`, we show that `(P, a OP b ~ C) => (C ~ c)`.

Then, we just have to solve problems of the form: `P => (a ~ b)`.

How did we come up with the second naming?  It was motivated by the
fact that we had `a + y = z1` in scope, which would give us `y = Y`
if we could prove that `z1 = Z`.

Perhaps, we could generate a new instance for every assumption
that mentions `y`?

    F1: a + b ~ x
    F2: b + c ~ Y         -- name
    F3: x + c ~ z1
    F5: a + y ~ z1
    F6: a + Y ~ Z1
    G: y ~ Y

In this case this works, but it seems a bit arbitrary.  Under what
circumstances would this be the right choice?

