Forward evaluation (add, multiply, exponentiate):

    p :: 5 * 3 ~ c

    mul_fun [5 3 c 5 3 15]  :: c ~ 15
      p                     :: 5 * 3 ~ c
      mul_def 5 3           :: 5 * 3 ~ 15


Backward evaluation (subtract, divide, logarithm, root):

    p :: 5 * a = 15
  
    mul_cancel_L [5 a 3]      :: a ~ 3
      leq_def 1 5             :: 1 <= 5
      eq_trans [5*a,15,5*3]   :: 5 * a ~ 5 * 3
        p                     :: 5 * a ~ 15
        eq_sym [5*3,15]       :: 15 ~ 5 * 3
          mul_def 5 3         :: 5 * 3 ~ 15



Chained forward evaluation:

    p :: 5 + a ~ b
    q :: 3 + b ~ c


Simplified equational form:

    8 + a       ~
    (3 + 5) + a ~
    3 + (5 + a) ~
    3 + b       ~
    c

Full proof:

    eq_trans [8+a,3+b,c]                :: 8 + a ~ c
      eq_trans [8+a,3+(5+a),3+b]        :: 8 + a ~ 3 + b
        eq_tarns [8+a,(3+5)+a,3+(5+a)]  :: 8 + a ~ 3 + (5 + a)
          add_cong [8,3+5,a,a]          :: 8 + a ~ (3 + 5) + a
            eq_sym [3+5,8]              :: 8 ~ 3 + 5
              add_def 3 5               :: 3 + 5 ~ 8
            eq_refl [a]                 :: a ~ a
          add_assoc [3,5,a]             :: (3 + 5) + a ~ 3 + (5 + a)
        add_cong [3,3,5+a,b]            :: 3 + (5 + a) ~ 3 + b
          eq_refl [3]                   :: 3 ~ 3
          p                             :: 5 + a ~ b
      q                                 :: 3 + b ~ c


We could avoid the nested `eq_trans` wiht a multi-arity variant, `eqs`:

    eqs [8+a,(3+5)+a,3+(5+a),3+b,c] :: 8 + a ~ c
      add_cong [8,3+5,a,a]            :: 8 + a ~ (3 + 5) + a
        eq_sym [3+5,8]                  :: 8 ~ 3 + 5
          add_def 3 5                   :: 3 + 5 ~ 8
        eq_refl [a]                     :: a ~ a
      add_assoc [3,5,a]               :: (3 + 5) + a ~ 3 + (5 + a)
      add_cong [3,3,5+a,b]            :: 3 + (5 + a) ~ 3 + b
        eq_refl [3]                     :: 3 ~ 3
        p                               :: 5 + a ~ b
     q                                :: 3 + b ~ c

The idea is that:

    eqs [a] []        = eq_refl [a]
    eqs (a:as) (p:ps) = let q     = eqs as ps
                            b ~ c = proves q
                        in eq_trans [a,b,c] [p,q]


Note that the main benefit to using `eqs` is that it avoids some
repeated instantiations: the seemingly more readable proof can be achieved
by just pretty printing the original in a different way (`eq_trans` are
the cons-nodes in the list of `eqs`).




