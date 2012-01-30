{- | To reason about order, we store the information about related terms
as a graph: the nodes are terms, and the edges are labelled with proofs,
providing evidence of the relation between the terms.
-}
module TcTypeNatsLeq
  ( Facts
  , prove
  , empty
  , addFact
  , AddFact(..)
  , toList
  , contains
  , extract
  ) where

import TcTypeNatsBase
import TcTypeNatsEval
import qualified Data.Map as M
import qualified Data.Set as S
import Text.PrettyPrint(vcat)
import Control.Monad(guard)
import Data.List(mapAccumL)
import Data.Maybe(maybeToList)

-- | A collection of facts about the ordering of terms.
newtype Facts = LM (M.Map Term Edges)

data Edge     = Edge { proof :: Proof, target :: Term }

data Edges    = Edges { above :: S.Set Edge -- proof: here   <= above
                      , below :: S.Set Edge -- proof: bellow <= here
                      }

instance Eq Edge where
  x == y  = target x == target y

instance Ord Edge where
  compare x y = compare (target x) (target y)

-- | Convert the graph representation (a node and its edges) to facts.
nodeFacts :: Term -> Edges -> [Fact]
nodeFacts x es = toFacts below lowerFact ++ toFacts above upperFact
  where
  toFacts list f = map f $ S.toList $ list es

  upperFact f    = Fact { factProp  = Prop Leq [x, target f]
                        , factProof = proof f
                        }

  lowerFact f    = Fact { factProp  = Prop Leq [target f, x]
                        , factProof = proof f
                        }

noEdges :: Edges
noEdges = Edges { above = S.empty, below = S.empty }

-- | An empty collection of facts about order.
empty :: Facts
empty = LM M.empty

-- | The list of ordering facts stored in the collection.
toList :: Facts -> [Fact]
toList (LM m) =
  do (from,edges) <- M.toList m
     edge         <- S.toList (above edges)
     let to = target edge
     guard (not (triv from to))
     return Fact { factProof = proof edge, factProp = Prop Leq [ from, to ] }

  where triv (Num {}) (Num {}) = True
        triv (Num 0 _) _       = True
        triv _       _         = False


-- | The edges immediately above a node.
immAbove :: Facts -> Term -> S.Set Edge
immAbove (LM m) t = case M.lookup t m of
                      Just edges -> above edges
                      Nothing    -> S.empty

-- | The edges immediately below a node.
immBelow :: Facts -> Term -> S.Set Edge
immBelow (LM m) t = case M.lookup t m of
                      Just edges -> below edges
                      Nothing    -> S.empty




-- | Check if there is an upward path from from the first node to the second.
-- The resulting proof object records the path.
reachable :: Facts -> Term -> Term -> Maybe Proof
reachable m smaller larger =
  search S.empty (S.singleton Edge { proof  = byLeqRefl smaller
                                   , target = smaller })
  where
  search visited todo =
    do (Edge { proof = pr, target = term }, rest) <- S.minView todo
       if term == larger
          then return pr
          else let updProof e = e { proof = byLeqTrans
                                              smaller
                                              term
                                              (target e)
                                              pr
                                              (proof e) }

                   new     = S.mapMonotonic updProof (immAbove m term)
                   vis     = S.insert term visited
                   notDone = S.filter (not . (`S.member` vis) . target)
          in search vis (notDone new `S.union` notDone rest)

findLowerBound :: Facts -> Term -> (Integer, Proof)
findLowerBound facts = snd . search M.empty
  where
  search cache t@(Num x _) = (cache, (x, byLeqRefl t))
  search cache t =
    case M.lookup t cache of
      Just b  -> (cache, b)
      Nothing ->
        let es          = S.toList (immBelow facts t)
            (cache1,bs) = mapAccumL search cache (map target es)
            jn (l,p) e  = (l, byLeqTrans (num l) (target e) t p (proof e))
            b           = foldr pickBigger (0, byLeq0 t) (zipWith jn bs es)
        in (M.insert t b cache1, b)

  pickBigger a@(x,_) b@(y,_) = if x > y then a else b

findUpperBound :: Facts -> Term -> Maybe (Proof, Integer)
findUpperBound facts = snd . search M.empty
  where
  search cache t@(Num x _) = (cache, Just (byLeqRefl t, x))
  search cache t =
    case M.lookup t cache of
      Just b  -> (cache, b)
      Nothing ->
        let es          = S.toList (immAbove facts t)
            (cache1,bs) = mapAccumL search cache (map target es)
            jn e mb     = do (p,u) <- mb
                             return (byLeqTrans t (target e) (num u)
                                                                (proof e) p, u)
            b           = foldr pickSmaller Nothing (zipWith jn es bs)
        in (M.insert t b cache1, b)

  pickSmaller Nothing x = x
  pickSmaller x Nothing = x
  pickSmaller (Just a@(_,x)) (Just b@(_,y)) = Just (if x < y then a else b)



{-

This diagram illustrates what we do when we link two nodes (leqLink).

We start with a situation like on the left, and we are adding an
edge from L to U.  The final result is illustrated on the right.

   Before    After

     a         a
    /|        /
   / |       /
  U  |      U\
  |  L        \L
  | /         /
  |/         /
  d         d

L: lower
U: upper
a: a member of "above uedges"  (uus)
d: a member of "below ledges"  (lls)
-}



link :: Proof -> (Term,Edges) -> (Term,Edges) -> Facts -> (Edges,Edges,Facts)

link ev (lower, ledges) (upper, uedges) (LM m) =

  let uus         = S.mapMonotonic target (above uedges)
      lls         = S.mapMonotonic target (below ledges)

      newLedges   = ledges { above =
                               S.insert (Edge { proof  = ev
                                              , target = upper
                                              })
                               $ S.filter (not . (`S.member` uus) . target)
                               $ above ledges
                           }
      newUedges   = uedges { below =
                               S.insert (Edge { proof  = ev
                                              , target = lower
                                              })
                               $ S.filter (not . (`S.member` lls) . target)
                               $ below uedges
                           }

{- The "undefined" in 'del' is OK because the proofs are not used in the
comparison and the set API seems to lack a function to get the same behavior.
Note that filter-ing is a little different because it has to traverse the
whole set while here we stop as soon as we found the element that is
to be removed. -}

      del x       = S.delete Edge { target = x, proof = undefined }


      adjAbove    = M.adjust (\e -> e { above = del upper (above e) })
      adjBelow    = M.adjust (\e -> e { below = del lower (below e) })
      fold f xs x = S.fold f x xs

  in ( newLedges
     , newUedges
     , LM $ M.insert lower newLedges
          $ M.insert upper newUedges
          $ fold adjAbove lls
          $ fold adjBelow uus
            m
     )

-- | Insert a new node in a collection of facts.
-- Returns the edges surrounding the new node.
--  * Variable nodes are always linked to 0 (directly or indirectly).
--  * Constant nodes are always linked to neighbouring constant nodes.
insNode :: Term -> Facts -> (Edges, Facts)
insNode t model@(LM m0) =
  case M.splitLookup t m0 of
    (_, Just r, _)  -> (r, model)
    (left, Nothing, right) ->
      let new           = noEdges
          ans1@(es1,m1) = ( new, LM (M.insert t new m0) )
      in case t of
           Var _ ->
             -- link to 0
             let zero         = num 0
                 (zes,zm)     = insNode zero m1    -- Should not modify es1
                 (_, es2, m2) = link (byLeq0 t) (zero,zes) (t,es1) zm
             in (es2, m2)
           Num m _ ->
             -- link to a smaller constnat, if any
             let ans2@(es2, m2) =
                   case toNum M.findMax left of
                     Nothing -> ans1
                     Just (n,l)  ->
                       let (_,x,y) = link (byLeqDef n m) l (t,es1) m1
                       in (x,y)
             -- link to a larger constant, if any
             in case toNum M.findMin right of
                  Nothing -> ans2
                  Just (n,u)  ->
                    let (x,_,y) = link (byLeqDef m n) (t,es2) u m2
                    in (x,y)

  where
  toNum f x = do guard (not (M.null x))
                 let r = f x
                 case fst r of
                   Num n _ -> return (n,r)
                   _       -> Nothing

-- | Try to find a proof that the first term is smaller then the second.
prove :: Facts -> Term -> Term -> Maybe Proof
prove model s t =
  let (_,m1) = insNode s model
      (_,m2) = insNode t m1
  in reachable m2 s t


{-| Remove the term from the model and return the facts immediately
associated with it.

This is useful when we want to improve a term: we remove it from the model,
improve the associated facts, and then add them back.
-}
extract :: Term -> Facts -> Maybe ([Fact], Facts)
extract term (LM m) =
  case M.updateLookupWithKey (\_ _ -> Nothing) term m of
    (Nothing, _)  -> Nothing
    (Just es, m1) -> Just
      ( nodeFacts term es
      , LM $ fold adjAbove (nodes below es)
           $ fold adjBelow (nodes above es) m1
      )
  where
  del         = S.delete Edge { target = term, proof = undefined }
  adjAbove    = M.adjust (\e -> e { above = del (above e) })
  adjBelow    = M.adjust (\e -> e { below = del (below e) })
  nodes f es  = S.mapMonotonic target (f es)
  fold f xs x = S.fold f x xs

-- | Check if the collection of facts mentions the given term.
contains :: Facts -> Term -> Bool
contains (LM m) t = case M.lookup t m of
                      Nothing -> False
                      Just _  -> True

instance PP Facts where
  pp = vcat . map pp . toList

-- | The result of trying to extend a collection of facts with a new one.
data AddFact = Added Facts    -- ^ The fact was added succesfully.
             | AlreadyKnown   -- ^ The fact was not added because it was known.
             | Improved Fact  -- ^ The fact was not added because there is
                              -- an equiavlent more useful fact.

-- | Try to add the fact that the first term is smaller then the second
-- (as evidenced by the proof).
addFact :: Proof -> Term -> Term -> Facts -> AddFact
addFact ev t1 t2 m0 =
  let (n1,m1)   = insNode t1 m0
      (n2,m2)   = insNode t2 m1

  in case reachable m2 t2 t1 of

       Nothing ->

         case reachable m2 t1 t2 of
           Nothing -> let (_,_,m3) = link ev (t1,n1) (t2,n2) m2
                      in Added m3
           Just _  -> AlreadyKnown

       {- We know the opposite: we don't add the fact
          but propose an equality instead. -}
       Just pOp -> Improved $
         Fact { factProof = byLeqAsym t1 t2 ev pOp
              , factProp  = Prop Eq [t1,t2]
              }

{- Monotonicity of the operators:

a <= x, b <= y
------------------ add mono
(a + b) <= (x + y)

a <= x, b <= y
------------------ mul mono
(a * b) <= (x * y)

a <= x, b <= y
------------------ exp mono
(a ^ b) <= (x ^ y)

-}

-- p : a + b = c
monoAddForward1 :: Proof -> Term -> Term -> Term -> Facts -> [Fact]
monoAddForward1 p a b c facts =
  [ Fact { factProp  = Prop Leq [a,c]
         , factProof = byMono Add [a,num 0,a,a,b,c]
                                  [byLeqRefl a, byLeq0 b, add0R a, p ]
         }

  , Fact { factProp  = Prop Leq [b,c]
         , factProof = byMono Add [num 0,b,b,a,b,c]
                                  [byLeq0 a, byRefl b, add0L a, p ]
         }
  , let (min_a, ma) = findLowerBound facts a
        (min_b, mb) = findLowerBound facts b
        ab          = min_a + min_b
    in Fact { factProp  = Prop Leq [num ab,c]
            , factProof = byMono Add [num min_a, num min_b, num ab, a, b, c]
                                     [ma,mb,defAdd min_a min_b ab,p]
            }
  ] ++
  [ Fact { factProp  = Prop Leq [c,num ab]
         , factProof = byMono Add [a,b,c,num max_a,num max_b, num ab]
                                  [ma,mb,p,defAdd max_a max_b ab]
         }
         | (ma,max_a) <- maybeToList (findUpperBound facts a)
         , (mb,max_b) <- maybeToList (findUpperBound facts b)
         , let ab = max_a + max_b
  ]

  where add0R t = Using Add0 [t] []
        add0L t = Using AddComm [t,num 0,t] [add0R t]
        defAdd x y z = Using (DefAdd x y z) [] []



-- p : a * b = c
monoMulForward1 :: Proof -> Term -> Term -> Term -> Facts -> [Fact]
monoMulForward1 p a b c facts =
  [ Fact { factProp  = Prop Leq [a,c]
         , factProof = byMono Mul [a,num 1,a,a,b,c]
                                  [byLeqRefl a, b1, mul1R a, p ]
         }
         | b1 <- maybeToList (prove facts (num 1) b)
  ] ++
  [ Fact { factProp  = Prop Leq [b,c]
         , factProof = byMono Mul [num 1,b,b,a,b,c]
                                  [a1, byRefl b, mul1L a, p ]
         }
         | a1 <- maybeToList (prove facts (num 1) a)
  ] ++
  [ let (min_a, ma) = findLowerBound facts a
        (min_b, mb) = findLowerBound facts b
        ab          = min_a * min_b
    in Fact { factProp  = Prop Leq [num ab,c]
            , factProof = byMono Mul [num min_a, num min_b, num ab, a, b, c]
                                     [ma,mb,defMul min_a min_b ab,p]
            }
  ] ++
  [ Fact { factProp  = Prop Leq [c,num ab]
         , factProof = byMono Mul [a,b,c,num max_a,num max_b, num ab]
                                  [ma,mb,p,defMul max_a max_b ab]
         }
         | (ma,max_a) <- maybeToList (findUpperBound facts a)
         , (mb,max_b) <- maybeToList (findUpperBound facts b)
         , let ab = max_a * max_b
  ]

  where mul1R t = Using Mul1 [t] []
        mul1L t = Using MulComm [t,num 1,t] [mul1R t]
        defMul x y z = Using (DefMul x y z) [] []



-- p : a ^ b = c
monoExpForward1 :: Proof -> Term -> Term -> Term -> Facts -> [Fact]
monoExpForward1 p a b c facts =
  [ Fact { factProp  = Prop Leq [a,c]
         , factProof = byMono Exp [a,num 1,a,a,b,c]
                                  [byLeqRefl a, b1, exp1R a, p ]
         }
         | b1 <- maybeToList (prove facts (num 1) b)
  ] ++
{- We could compose with x <= 2^x...?
  [ Fact { factProp  = Prop Leq [2^b,c]
         , factProof = byMono Exp [num 2,b,2^b,a,b,c]
                                  [a1, byRefl b, defn, p ]
         }
         | a1 <- maybeToList (prove facts (num 2) a)
  ] ++ -}

  [ let (min_a, ma) = findLowerBound facts a
        (min_b, mb) = findLowerBound facts b
        ab          = min_a ^ min_b
    in Fact { factProp  = Prop Leq [num ab,c]
            , factProof = byMono Exp [num min_a, num min_b, num ab, a, b, c]
                                     [ma,mb,defExp min_a min_b ab,p]
            }
  ] ++
  [ Fact { factProp  = Prop Leq [c,num ab]
         , factProof = byMono Exp [a,b,c,num max_a,num max_b, num ab]
                                  [ma,mb,p,defExp max_a max_b ab]
         }
         | (ma,max_a) <- maybeToList (findUpperBound facts a)
         , (mb,max_b) <- maybeToList (findUpperBound facts b)
         , let ab = max_a ^ max_b
  ]

  where exp1R t = Using Root1 [t] []    -- a ^ 1 = a
        defExp x y z = Using (DefExp x y z) [] []




{-

Interval forward:

x + y = z          min x + min y <= z <= max x + max y
x * y = z          min x * min y <= z <= max x * max y
x ^ y = z          min x ^ min y <= z <= max x ^ max y


Interval backward:

x + y = z        max (0,min z - max y) <= x <= max z - min y
x * y = z        ceil(min z / max y) <= x <= floor(max z / min y)
  Note that we assume that dividing non-0 values by infinity (i.e.,
    when there is no upper limit for `y`) gives a small yet non-0 value,
    so `ceil` will round to 1.)

    Example: min z = 5, max y = 3       -- 2 <= x
    Example: min z = 5, max y = Nothing -- 1 <= x

x ^ y = z    ceil (root (min z0) (max y)) x <= floor (root (max z0) (min y))
             ceil (log  (min z0) (max x)) y <= floor (log  (max z0) (min x))


Justificatin of forward intreval:


These also justify the current ordering rules:
  (x + y = z, x <= x, 0 <= y) => x <= z     (by add mono)
  (x * y = z, x <= x, 1 <= y) => x <= z     (by mul mono)
  (x ^ y = z, x <= x, 1 <= y) => x <= z     (by exp mono)
  (x ^ y = z, 2 <= x, y <= y) => (2^y) <= z


Justificatin of backward intreval:

(a + c) <= (b + c)
------------------  sub_c mono
a <= b

(a * c) <= (b * c), 1 <= c
--------------------------  div_by_c mono
a <= b

(a ^ c) <= (b <= c), 1 <= c
--------------------------- root_cth mono
a <= c

(c ^ a) <= (c ^ b), 2 <= c
-------------------------- log_base_c mono
a <= c


Hm, do we really need the backward mono rules?
Here are proofs of the (*) backward rules, just using (*) monotonicity.
They do use the deiniftions of ceil&floor, as expected.

goal: x * y = z   => ceil(min_z/max_y) <= x
proof:
  let n = ceil(min_z/max_y)
  hence n is the smallest s.t., min_z <= n * max_y.
  but min_z <= z = x * y <= x * max_y.
  hence n <= x.

goal: x * y = z => x <= floor(max_z/min_y)
proof
  let n = floor(max_z/min_y)
  hence n is the largest s.t. n * min_y <= max_z
  but x * min_y <= x * y = z <= max_z
  hence x <= n.

The central rule for the proofs:

b <= x * a
--------------
ceil(b/a) <= x

x * a <= b
---------------
x <= floor(b/a)

These do resemble the div_by_c rule...

-}

