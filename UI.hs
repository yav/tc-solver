{-# LANGUAGE DeriveDataTypeable #-}
import Prelude hiding (catch)
import Control.Exception
import System.IO
import Data.Typeable
import Data.List
import Control.Monad
import Network
import Data.Char
import qualified Data.Map as M
import Numeric
import System.Process
import System.Exit(ExitCode(..))
import Text.ParserCombinators.ReadP
import System.Info
import Text.PrettyPrint hiding (char)


import TcTypeNatsBase
import TcTypeNatsFacts as Facts
import TcTypeNatsProps as Props
import TcTypeNats
import TcTypeNatsStandAlone


port :: PortNumber
port = 8000

info :: String -> IO ()
info = putStrLn

--------------------------------------------------------------------------------

main :: IO ()
main = withSocketsDo
     $ do s <- listenOn (PortNumber port)
          info $ "Listening on port " ++ show port
          loop s initS `finally` sClose s
  where loop s st = loop s =<< onConnect st =<< accept s

onConnect :: S -> (Handle, HostName, PortNumber) -> IO S
onConnect s (h,host,p) =
  do info $ "Connection from " ++ show host ++ ":" ++ show p
     hSetEncoding h utf8
     hSetNewlineMode h NewlineMode { inputNL = CRLF, outputNL = CRLF }
     (url,_) <- getRequest h
     case parse url of
       Nothing -> initPage h >> return s
       Just cmd ->
         do let s1 = processCmd cmd s
                wis = case cmd of
                        AddC _ x -> x
                        _       -> []
            respond h "200 OK" (list [ list (map renderWI wis)
                                     , renderIS (inertSet s1)
                                     ]
                               )
            return s1

initPage h =
  do txt <- readFile "UI.html"
     info "Loding start page"
     hPutStrLn h $ unlines
       [ "HTTP/1.1 200 OK"
       , "Content-Type: text/html; charset=UTF-8"
       ]
     hSetNewlineMode h noNewlineTranslation
     hPutStr h txt -- XXX: encode utf-8
     hClose h
     info "Done with start page"



--------------------------------------------------------------------------------
data Cmd = AddC Int [WorkItem] | RmC Int
data WorkItem = Given Fact | Wanted Goal

data S = S { entered  :: M.Map Int [WorkItem]
           , inertSet :: Maybe SolverS
           }

initS :: S
initS = S { entered = M.empty, inertSet = Just initSolverS }


addWorkItemsUI :: (Int,[WorkItem]) -> SolverS -> Maybe SolverS
addWorkItemsUI (n,ws) is = addWorkItems is1 ('w' : show n) (length ws + 1)
  where is1 = is { ssTodoGoals = [ w | Wanted w <- ws ]
                 , ssTodoFacts = Props.fromList [ g | Given g  <- ws ]
                 }

addWorkItems :: SolverS -> String -> Int -> Maybe SolverS
addWorkItems is r s = fst `fmap` runTCN (addWorkItemsM is) r s

processCmd :: Cmd -> S -> S
processCmd cmd s =
  case cmd of
    AddC x wi -> S { entered   = M.insert x wi (entered s)
                   , inertSet  = addWorkItemsUI (x,wi) =<< inertSet s
                   }
    RmC x     -> S { entered   = ents
                   , inertSet  = foldM (flip addWorkItemsUI)
                                       initSolverS
                                       (M.toList ents)
                   }
      where ents = M.delete x (entered s)



-- HTTP ------------------------------------------------------------------------
type Request  = (URL, [Header])
type URL      = String
type Header   = (String,String)

data Err      = BadReqStart String
              | BadReqHeader String
                deriving (Show,Typeable)

instance Exception Err



respond :: Handle -> String -> String -> IO ()
respond h resp txt =
  do hPutStrLn h $ unlines
       [ "HTTP/1.1 " ++ resp
       , "Content-Type: application/json; charset=UTF-8"
       ]
     info txt
     hSetNewlineMode h noNewlineTranslation
     hPutStr h txt -- XXX: encode utf-8
     hClose h

getRequest :: Handle -> IO Request
getRequest h =
  do first <- hGetLine h
                `catch` \(SomeException _) -> throwIO (BadReqStart "")
     case words first of
       ["GET",u,"HTTP/1.1"] ->
         do hs <- getHeaders h []
            return (u, hs)
       _ -> throwIO (BadReqStart first)

getHeaders :: Handle -> [Header] -> IO [Header]
getHeaders h prev =
  do l <- hGetLine h
                `catch` \(SomeException _) -> throwIO (BadReqHeader "")
     case l of
       "" -> return prev
       _  -> case break (':' ==) l of
               (as,_:bs) -> getHeaders h ((as, trim bs) : prev)
               _         -> throwIO (BadReqHeader l)
  where trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

--------------------------------------------------------------------------------
-- Protocol


parse :: URL -> Maybe Cmd
parse url =
  case break (== '?') url of
    ("/add",_:rest) ->
      case break (== '&') rest of
        (ntxt,_:p) ->
          do n  <- readMb ntxt
             wi <- parseWI n p
             return (AddC n wi)
        _ -> mzero

    ("/rm",_:ntxt) ->
      do n <- readMb ntxt
         return (RmC n)

    _ -> Nothing

parseWI :: Int -> String -> Maybe [WorkItem]
parseWI n txt =
  case break (== '&') txt of
    ("Wanted", _:p) -> zipWith mkGoal [ 1 .. ] `fmap` parseProp n p
    ("Given", _:p)  -> zipWith mkFact [ 1 .. ] `fmap` parseProp n p
    _               -> Nothing
  where
  mkGoal x p = Wanted Goal { goalName = mkName "w" x, goalProp = p }
  mkFact x p = Given Fact { factProof = ByAsmp (mkName "g" x), factProp = p }
  mkName p x  = strEvVar (p ++ show n ++ "_" ++ show (x :: Integer))


parseProp :: Int -> String -> Maybe [Prop]
parseProp n txt =
  do s <- dec txt
     readMb' (readP_to_S (pEqn n)) s
  where
  dec ('%' : x : y : xs) = do n1 <- readMb' readHex [x,y]
                              fmap (toEnum n1 :) (dec xs)
  dec []                 = return []
  dec (x : xs)           = (x:) `fmap` dec xs

renderWI :: WorkItem -> String
renderWI (Wanted w) = list [ str "Wanted", ppp (goalName w) (goalProp w) ]
  where ppp x y = str (show (pprEvVar x) ++ ": " ++ show (pp y))
renderWI (Given  f) = list [str "Given",  str $ show $ pp $ factProp f ]

renderIS :: Maybe SolverS -> String
renderIS Nothing = list [ list [ str "Wanted", str "(inconsistent)" ]
                        , list [ str "Given",  str "(inconsistent)" ]
                        ]
renderIS (Just ss) =
  list ( [ renderWI (Given g)  | g <- Facts.toList (facts xs)  ] ++
         [ renderWI (Wanted w) | w <- Props.toList (goals xs) ] ++
         [ list [ show "Proof", show $ ppp p ] | p <- ps ]
       )
  where ppp (x,y) = show (pprEvVar x <+> text ":" <+> pp y)
        xs = ssInerts ss
        ps = ssSolved ss


type JSON = String

str :: String -> JSON
str x = show x

list :: [JSON] -> JSON
list xs = "[" ++ concat (intersperse "," xs) ++ "]"

pEqn :: Int -> ReadP [Prop]
pEqn n =
  msum
    [ do (t1,op,t2,n',es1) <- pTerm pref 0
         tchar '='
         (t3,_,es2) <- pAtom pref n'
         return (Prop op [t1,t2,t3] : es1 ++ es2)
    , do (t1,n1,es1) <- pAtom pref 0
         r <- pRel
         (t2,_,es2) <- pAtom pref n1
         return (Prop r [t1,t2] : es1 ++ es2)
    ]
  where pref = n

pTerm :: Int -> Int -> ReadP (Term,Pred,Term,Int,[Prop])
pTerm pref n0 =
  do (t1,n1,es1) <- pAtom pref n0
     op <- pOp
     (t2,n2,es2) <- pAtom pref n1
     return (t1,op,t2,n2,es1++es2)

pAtom :: Int -> Int -> ReadP (Term, Int, [Prop])
pAtom pref n =
  do _ <- munch isSpace
     msum
       [ do x <- readS_to_P reads
            return (Num x Nothing, n, [])
       , do a <- satisfy (\x -> isAlpha x || x == '_')
            as <- munch (\x -> isAlphaNum x || x == '_')
            return (Var $ V $ strXi $ a:as, n, [])
       , do (t1,op,t2,n',es) <- between (tchar '(') (tchar ')') (pTerm pref n)
            let x = Var (newVar pref n')
            return (x, n'+1, Prop op [t1,t2,x] : es)
       ]

pRel :: ReadP Pred
pRel = msum [ tchar '=' >> return Eq
            , tchar '<' >> char '=' >> return Leq
            ]

pOp :: ReadP Pred
pOp = msum [ tchar '+' >> return Add
           , tchar '*' >> return Mul
           , tchar '^' >> return Exp
           ]

newVar :: Int -> Int -> Var
newVar pref n = V $ strXi $ (vars !! n) ++ "_" ++ show pref
  where vars      = concatMap chunk [ 0 :: Integer .. ]
        toVar c a = if a == 0 then [c] else c : show a
        chunk n1  = map (`toVar` n1) [ 'a' .. 'z' ]

tchar :: Char -> ReadP ()
tchar p = munch isSpace >> char p >> return ()

test :: ReadP a -> String -> Maybe a
test p ys = readMb' (readP_to_S p) ys

--------------------------------------------------------------------------------
readMb     :: Read a => String -> Maybe a
readMb x    = readMb' reads x

readMb'    :: ReadS a -> String -> Maybe a
readMb' f x = case f x of
                [(a,"")] -> Just a
                _ -> Nothing



--------------------------------------------------------------------------------

data SolverS = SolverS
  { ssTodoFacts :: Props Fact
  , ssTodoGoals :: [Goal]
  , ssSolved    :: [(EvVar,Proof)]
  , ssInerts    :: Inerts
  }


initSolverS :: SolverS
initSolverS = SolverS
  { ssTodoGoals = []
  , ssTodoFacts = Props.empty
  , ssSolved    = []
  , ssInerts    = noInerts
  }


-- | The final state should have empty 'todo*' queues.
addWorkItemsM :: SolverS -> TCN SolverS

addWorkItemsM ss0 =
  case getFact ss0 of
    Just (fact, ss1) ->
      do r <- insertFact fact (ssInerts ss1)
         addWorkItemsM (nextState r ss1)

    Nothing ->
      case getGoal ss0 of
       Just (goal, ss1) ->
         do r <- insertGoal goal (ssInerts ss1)
            addWorkItemsM (nextState r ss1)

       Nothing -> return ss0




{- | When processing facts, it is more
efficient if we first process equalities, then order and, finally, all other
facts.  To make this easy, we store unprocessed facts as 'Prpos' instead
of just using a list.

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

getFact :: SolverS -> Maybe (Fact, SolverS)
getFact s = case getOne (ssTodoFacts s) of
              Nothing     -> Nothing
              Just (f,fs) -> Just (f, s { ssTodoFacts = fs })

getGoal :: SolverS -> Maybe (Goal, SolverS)
getGoal s = case ssTodoGoals s of
              []     -> Nothing
              g : gs -> Just (g, s { ssTodoGoals = gs })

nextState :: InsertInert -> SolverS -> SolverS
nextState r s =
  SolverS { ssTodoFacts = Props.union (newFacts r) (ssTodoFacts s)
          , ssTodoGoals = newGoals r ++ ssTodoGoals s
          , ssInerts    = newInerts r
          , ssSolved    = solvedGoals r ++ ssSolved s
          }

--------------------------------------------------------------------------------


