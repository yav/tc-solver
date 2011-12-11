{-
Reasoning About Order

To reason about order, we store the information about related terms
as a graph: the nodes are terms, and the edges are labelled with proofs,
providing evidence of the relation between the terms.
-}
module TcTypeNatsLeq where

import TcTypeNatsBase
import qualified Data.Map as M
import qualified Data.Set as S
import Text.PrettyPrint
import Control.Monad(guard)

newtype LeqFacts = LM (M.Map Term LeqEdges)

data LeqEdge = LeqEdge { leProof :: Proof, leTarget :: Term }

data LeqEdges = LeqEdges { lnAbove :: S.Set LeqEdge -- proof: here   <= above
                         , lnBelow :: S.Set LeqEdge -- proof: bellow <= here
                         }



instance Eq LeqEdge where
  x == y  = leTarget x == leTarget y

instance Ord LeqEdge where
  compare x y = compare (leTarget x) (leTarget y)

leqNodeFacts :: Term -> LeqEdges -> [Fact]
leqNodeFacts x es = toFacts lnBelow lowerFact ++ toFacts lnAbove upperFact
  where
  toFacts list f = map f $ S.toList $ list es

  upperFact f    = Fact { factProp  = Prop Leq [x, leTarget f]
                        , factProof = leProof f
                        }

  lowerFact f    = Fact { factProp  = Prop Leq [leTarget f, x]
                        , factProof = leProof f
                        }

noLeqEdges :: LeqEdges
noLeqEdges = LeqEdges { lnAbove = S.empty, lnBelow = S.empty }


noLeqFacts :: LeqFacts
noLeqFacts = LM M.empty

leqFactsToList :: LeqFacts -> [Fact]
leqFactsToList (LM m) =
  do (from,edges) <- M.toList m
     edge         <- S.toList (lnAbove edges)
     let to = leTarget edge
     guard (not (triv from to))
     return Fact { factProof = leProof edge, factProp = Prop Leq [ from, to ] }

  where triv (Num {}) (Num {}) = True
        triv (Num 0 _) _       = True
        triv _       _         = False



leqImmAbove :: LeqFacts -> Term -> S.Set LeqEdge
leqImmAbove (LM m) t = case M.lookup t m of
                         Just edges -> lnAbove edges
                         Nothing    -> S.empty


leqReachable :: LeqFacts -> Term -> Term -> Maybe Proof
leqReachable m smaller larger =
  search S.empty (S.singleton LeqEdge { leProof  = byLeqRefl smaller
                                      , leTarget = smaller })
  where
  search visited todo =
    do (LeqEdge { leProof = proof, leTarget = term }, rest) <- S.minView todo
       if term == larger
          then return proof
          else let updProof e = e { leProof = byLeqTrans
                                                smaller
                                                term
                                                (leTarget e)
                                                proof
                                                (leProof e) }

                   new     = S.mapMonotonic updProof (leqImmAbove m term)
                   vis     = S.insert term visited
                   notDone = S.filter (not . (`S.member` vis) . leTarget)
          in search vis (notDone new `S.union` notDone rest)




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
a: a member of "lnAbove uedges"  (uus)
d: a member of "lnBelow ledges"  (lls)
-}



leqLink :: Proof -> (Term,LeqEdges) -> (Term,LeqEdges) -> LeqFacts ->
                                                  (LeqEdges,LeqEdges,LeqFacts)

leqLink proof (lower, ledges) (upper, uedges) (LM m) =

  let uus         = S.mapMonotonic leTarget (lnAbove uedges)
      lls         = S.mapMonotonic leTarget (lnBelow ledges)

      newLedges   = ledges { lnAbove =
                               S.insert (LeqEdge { leProof  = proof
                                                 , leTarget = upper
                                                 })
                               $ S.filter (not . (`S.member` uus) . leTarget)
                               $ lnAbove ledges
                           }
      newUedges   = uedges { lnBelow =
                               S.insert (LeqEdge { leProof  = proof
                                                 , leTarget = lower
                                                 })
                               $ S.filter (not . (`S.member` lls) . leTarget)
                               $ lnBelow uedges
                           }

{- The "undefined" in 'del' is OK because the proofs are not used in the
comparison and the set API seems to lack a function to get the same behavior.
Note that filter-ing is a little different because it has to traverse the
whole set while here we stop as soon as we found the element that is
to be removed. -}

      del x       = S.delete LeqEdge { leTarget = x, leProof = undefined }


      adjAbove    = M.adjust (\e -> e { lnAbove = del upper (lnAbove e) })
      adjBelow    = M.adjust (\e -> e { lnBelow = del lower (lnBelow e) })
      fold f xs x = S.fold f x xs

  in ( newLedges
     , newUedges
     , LM $ M.insert lower newLedges
          $ M.insert upper newUedges
          $ fold adjAbove lls
          $ fold adjBelow uus
            m
     )

leqInsNode :: Term -> LeqFacts -> (LeqEdges, LeqFacts)
leqInsNode t model@(LM m0) =
  case M.splitLookup t m0 of
    (_, Just r, _)  -> (r, model)
    (left, Nothing, right) ->
      let new           = noLeqEdges
          ans1@(es1,m1) = ( new, LM (M.insert t new m0) )
      in case t of
           Var _ ->
             -- link to 0
             let zero         = num 0
                 (zes,zm)     = leqInsNode zero m1    -- Should not modify es1
                 (_, es2, m2) = leqLink (byLeq0 t) (zero,zes) (t,es1) zm
             in (es2, m2)
           Num m _ ->
             -- link to a smaller constnat, if any
             let ans2@(es2, m2) =
                   case toNum M.findMax left of
                     Nothing -> ans1
                     Just (n,l)  ->
                       let (_,x,y) = leqLink (byLeqDef n m) l (t,es1) m1
                       in (x,y)
             -- link to a larger constant, if any
             in case toNum M.findMin right of
                  Nothing -> ans2
                  Just (n,u)  ->
                    let (x,_,y) = leqLink (byLeqDef m n) (t,es2) u m2
                    in (x,y)

  where
  toNum f x = do guard (not (M.null x))
                 let r = f x
                 case fst r of
                   Num n _ -> return (n,r)
                   _       -> Nothing


{-
leqFactsAffectedBy :: LeqFacts -> Subst -> Bool
leqFactsAffectedBy (LM m) = any affects . substDom
  where affects x = case M.lookup (Var x) (fst (M.split (num 0) m)) of
                      Nothing -> False
                      _       -> True
-}

leqProve :: LeqFacts -> Term -> Term -> Maybe Proof
leqProve model s t =
  let (_,m1) = leqInsNode s model
      (_,m2) = leqInsNode t m1
  in leqReachable m2 s t


{- Remove the term from the model, and return the facts immediately
associated with ot.

This is useful when we want to improve a term: we remove it from the model,
improve the associated facts, and then add them back.
-}
leqExtract :: Term -> LeqFacts -> Maybe ([Fact], LeqFacts)
leqExtract term (LM m) =
  case M.updateLookupWithKey (\_ _ -> Nothing) term m of
    (Nothing, _)  -> Nothing
    (Just es, m1) -> Just
      ( leqNodeFacts term es
      , LM $ fold adjAbove (nodes lnBelow es)
           $ fold adjBelow (nodes lnAbove es) m1
      )
  where
  del         = S.delete LeqEdge { leTarget = term, leProof = undefined }
  adjAbove    = M.adjust (\e -> e { lnAbove = del (lnAbove e) })
  adjBelow    = M.adjust (\e -> e { lnBelow = del (lnBelow e) })
  nodes f es  = S.mapMonotonic leTarget (f es)
  fold f xs x = S.fold f x xs

leqContains :: LeqFacts -> Term -> Bool
leqContains (LM m) t = case M.lookup t m of
                         Nothing -> False
                         Just _  -> True

instance PP LeqFacts where
  pp = vcat . map pp . leqFactsToList


