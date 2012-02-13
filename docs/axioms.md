These are the axioms in non-canonicalized form.


General properties of equality:

    eq_refl   :: forall a.                       (a ~ a)
    eq_trans  :: forall a b c. (a ~ b, b ~ c) => (a ~ c)
    eq_sym    :: forall a b.   (a ~ b)        => (b ~ a)


Interactions between equality and any function or predicate.
Here, insantiated to the function and predicate symbols of the theory:

    add_fun   :: forall a b c1 c2. (a + b ~ c1, a + b ~ c2) => (c1 ~ c2)
    mul_fun   :: forall a b c1 c2. (a * b ~ c1, a * b ~ c2) => (c1 ~ c2)
    exp_fun   :: forall a b c1 c2. (a ^ b ~ c1, a ^ b ~ c2) => (c1 ~ c2)
    
    add_cong  :: forall a b x y. (a ~ x, b ~ y)         => (a + b ~ x + y)
    mul_cong  :: forall a b x y. (a ~ x, b ~ y)         => (a * b ~ x * y)
    exp_cong  :: forall a b x y. (a ~ x, b ~ y)         => (a ^ b ~ x ^ y)
    leq_cong  :: forall a b x y. (a ~ x, b ~ y, a <= b) => (x <= y)


Definitions on literals (`a` and `b` are concrete literals):

    add_def a b   :: a + b ~ $(a + b)
    mul_def a b   :: a * b ~ $(a * b)
    exp_def a b   :: a ^ b ~ $(a ^ b)
    leq_def a b   :: $(a <= b) => (a <= b)


Units:

    add_unit_R    :: forall a. a + 0 ~ a
    mul_unit_R    :: forall a. a * 1 ~ a
    exp_unit_R    :: forall a. a ^ 1 ~ a

Anihilators:

    mul_anih_R    :: forall a. a * 0 ~ 0
    exp_anih_R    :: forall a. a ^ 0 ~ 1
    exp_anih_L    :: forall a. (1 <= a) => 0 ^ a ~ 0

Commutativity:

    add_comm      :: forall a b. a + b ~ b + a
    mul_comm      :: forall a b. a * b ~ b * a

Associativity:

    add_assoc     :: forall a b c. (a + b) + c ~ a + (b + c)
    mul_assoc     :: forall a b c. (a * b) * c ~ a * (b * c)


Distributivity:

    add_mul_distr :: forall a b c. (a + b) * c ~ (a * c) + (b * c)
    mul_exp_distr :: forall a b c. (a * b) ^ c ~ (a ^ c) * (b ^ c)


Exponentiation and other operators:

    exp_add       :: forall a b c. a ^ (b + c) ~ (a ^ b) * (a ^ c)
    exp_mul       :: forall a b c. a ^ (b * c) ~ (a ^ b) ^ c

Cancellation:

    add_cancel_L  :: forall a b1 b2.  (        a + b1 ~ a + b2) => (b1 ~ b2)
    mul_cancel_L  :: forall a b1 b2.  (1 <= a, a * b1 ~ a * b2) => (b1 ~ b2)
    exp_cancel_L  :: forall a b1 b2.  (2 <= a, a ^ b1 ~ a ^ b2) => (b1 ~ b2)
    exp_cancel_R  :: forall a1 a2 b.  (1 <= b, a1 ^ b ~ a2 ^ b) => (a1 ~ a2)


General properties of order:

    leq_refl      :: forall a.                         (a <= a)
    leq_trans     :: forall a b c. (a <= b, b <= c) => (a <= c)
    leq_antisym   :: forall a b.   (a <= b, b <= a) => (a ~ b)

Monotonicity (congruence with respect to order):

    add_mono      :: forall a b x y. (a <= x, b <= y) => (a + b <= x + y)
    mul_mono      :: forall a b x y. (a <= x, b <= y) => (a * b <= x * y)
    exp_mono      :: forall a b x y. (a <= x, b <= y) => (a ^ b <= x ^ y)

Cancellation and order:

    leq_add_cancel_L :: forall a b1 b2. (        a + b1 <= a + b2) => (b1 <= b2)
    leq_mul_cancel_L :: forall a b1 b2. (1 <= a, a * b1 <= a * b2) => (b1 <= b2)
    leq_exp_cancel_L :: forall a b1 b2. (2 <= a, a ^ b1 <= a ^ b2) => (b1 <= b2)
    leq_exp_cancel_R :: forall a1 a2 b. (1 <= b, a1 ^ b <= a2 ^ b) => (a1 <= a2)


Perhaps...
----------

Totality.  These do not fit with the standard evidence structure because
of the existential.  They are useful for naming terms (i.e., the existential
is always eliminated by introducing a fresh variable).

    -- conceptual
    add_tot       :: forall a b. exists c. a + b ~ c
    mul_tot       :: forall a b. exists c. a * b ~ c
    exp_tot       :: forall a b. exists c. a ^ b ~ c

    -- To make things fit, where `c` should start off as a fresh variable.
    add_tot a b c :: a + b ~ c
    mul_tot a b c :: a * b ~ c
    exp_tot a b c :: a ^ b ~ c

iMaybe this sould be done with some sort of `let` construct.



