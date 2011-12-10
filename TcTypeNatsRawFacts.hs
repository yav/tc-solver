{- A collection of unprocessed facts.  When processing facts, it is more
efficient if we first process equalities, then orider and, finally, all other
facts.  To make this easy, we store unprocessed facts as 'RawFacts' instead
of just using [Fact].

We add equalities first because they might lead to improvements that,
in turn, would enable the discovery of additional facts.  In particular, if a
presently known fact gets improved, then the old fact is removed from the
list of known facts, and its improved version is added as new work.  Thus,
if we process equalities first, we don't need to do any of this "restarting".

For similar reasons we process ordering predicates before others: they
make it possible for certain conditional rules to fire.  For example,
the cancellation rule for multiplication requires that the argument that
is being cancelled is greater than 0.
-}

module TcTypeNatsRawFacts where

import TcTypeNatsBase


data RawFacts = RawFacts { rawEqFacts  :: [Fact]
                         , rawLeqFacts :: [Fact]
                         , rawFacts    :: [Fact]
                         }

noRawFacts :: RawFacts
noRawFacts = RawFacts { rawEqFacts  = []
                      , rawLeqFacts = []
                      , rawFacts    = []
                      }

insertRawFact :: Fact -> RawFacts -> RawFacts
insertRawFact f fs = case propPred f of
                       Eq  -> fs { rawEqFacts  = f : rawEqFacts fs }
                       Leq -> fs { rawLeqFacts = f : rawLeqFacts fs }
                       _   -> fs { rawFacts    = f : rawFacts fs }

oneRawFact :: Fact -> RawFacts
oneRawFact f = insertRawFact f noRawFacts

appendRawFacts :: RawFacts -> RawFacts -> RawFacts
appendRawFacts fs1 fs2 =
  RawFacts { rawEqFacts  = rawEqFacts  fs1 ++ rawEqFacts  fs2
           , rawLeqFacts = rawLeqFacts fs1 ++ rawLeqFacts fs2
           , rawFacts    = rawFacts    fs1 ++ rawFacts    fs2
           }

getRawFact :: RawFacts -> Maybe (Fact, RawFacts)
getRawFact fs =
  case rawEqFacts fs of
    e : es -> return (e, fs { rawEqFacts = es })
    []     -> case rawLeqFacts fs of
                l : ls -> return (l, fs { rawLeqFacts = ls })
                []     -> case rawFacts fs of
                            o : os -> return (o, fs { rawFacts = os })
                            []     -> Nothing

rawFactsFromList :: [Fact] -> RawFacts
rawFactsFromList = foldr insertRawFact noRawFacts

rawFactsToList :: RawFacts -> [Fact]
rawFactsToList fs = rawEqFacts fs ++ rawLeqFacts fs ++ rawFacts fs



