{-# LANGUAGE DeriveDataTypeable #-}
import Prelude hiding (catch)
import Control.Exception
import System.IO
import Data.Typeable
import Control.Monad
import Network
import Data.Char
import qualified Data.Map as M
import Numeric
import Data.Maybe(fromMaybe)
import System.Process
import System.Exit(ExitCode(..))

import Notes
import Test


port :: PortNumber
port = 8000

info :: String -> IO ()
info = putStrLn

--------------------------------------------------------------------------------

main :: IO ()
main = withSocketsDo
     $ do s <- listenOn (PortNumber port)
          info $ "Listening on port " ++ show port
          ExitSuccess <- system "gnome-open UI.html"
          loop s initS `finally` sClose s
  where loop s st = loop s =<< onConnect st =<< accept s

onConnect :: S -> (Handle, HostName, PortNumber) -> IO S
onConnect s (h,host,p) =
  do info $ "Connection from " ++ show host ++ ":" ++ show p
     hSetEncoding h utf8
     hSetNewlineMode h NewlineMode { inputNL = CRLF, outputNL = CRLF }
     (url,_) <- getRequest h
     case parse url of
       Nothing -> respond h "402 Bad request" "[]" >> return s
       Just cmd ->
         do let s1 = processCmd cmd s
            respond h "200 OK" (renderIS (inertSet s1))
            return s1




--------------------------------------------------------------------------------
data Cmd = AddC Int WorkItem | RmC Int
type WorkItem = (PropKind,Prop)
data PropKind = Given | Wanted deriving Show

data S = S { entered  :: M.Map Int WorkItem
           , inertSet :: Maybe PropSet
           }

initS :: S
initS = S { entered = M.empty, inertSet = Just emptyPropSet }


addWorkItemsUI :: [WorkItem] -> PropSet -> Maybe PropSet
addWorkItemsUI ws is = addWorkItems set is
  where set = PropSet { wanted = [ w | (Wanted,w) <- ws ]
                      , given  = [ g | (Given,g) <- ws ]
                      }

processCmd :: Cmd -> S -> S
processCmd cmd s =
  case cmd of
    AddC x wi -> S { entered   = M.insert x wi (entered s)
                   , inertSet  = addWorkItemsUI [wi] =<< inertSet s
                   }
    RmC x     -> S { entered   = ents
                   , inertSet  = addWorkItemsUI (M.elems ents) emptyPropSet
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
       , "Access-Control-Allow-Origin: *"
       ]
     hSetNewlineMode h noNewlineTranslation
     hPutStr h txt -- XXX: encode utf-8
     hClose h

getRequest :: Handle -> IO Request
getRequest h =
  do first <- hGetLine h
     case words first of
       ["GET",u,"HTTP/1.1"] ->
         do hs <- getHeaders h []
            return (u, hs)
       _ -> throwIO (BadReqStart first)

getHeaders :: Handle -> [Header] -> IO [Header]
getHeaders h prev =
  do l <- hGetLine h
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
             wi <- parseWI p
             return (AddC n wi)
        _ -> mzero

    ("/rm",_:ntxt) ->
      do n <- readMb ntxt
         return (RmC n)

    _ -> Nothing

parseWI :: String -> Maybe WorkItem
parseWI txt =
  case break (== '&') txt of
    ("Wanted", _:p) -> fmap ((,) Wanted) $ parseProp p
    ("Given", _:p)  -> fmap ((,) Given) $ parseProp p
    _               -> Nothing

parseProp :: String -> Maybe Prop
parseProp txt =
  do s <- dec txt
     case break op s of
       (as,'<' : '=' : bs) -> Leq `fmap` parseT as `ap` parseT bs
       (as,'=': bs)        -> Eq `fmap` parseT as `ap` parseT bs
       (as, opc : rest) ->
          case break (== '=') rest of
            (bs,_:cs) -> EqFun theOp `fmap` parseT as `ap` parseT bs
                                                      `ap` parseT cs
              where theOp = case opc of
                              '+' -> Add
                              '*' -> Mul
                              '^' -> Exp
                              _ -> error "bug: unexpected op"
            _ -> Nothing
       _ -> Nothing

  where
  dec ('%' : x : y : xs) = do n <- readMb' readHex [x,y]
                              fmap (toEnum n :) (dec xs)
  dec []                 = return []
  dec (x : xs)           = (x:) `fmap` dec xs

  parseT "" = Nothing
  parseT t = return $ fromMaybe (Var z) (num `fmap` readMb z)
    where z = trim t
  trim     = reverse . dropWhile isSpace . reverse . dropWhile isSpace

  op x = x `elem` "+*^<="

renderWI :: WorkItem -> [String]
renderWI (x,y) = [ show x, show y ]

renderIS :: Maybe PropSet -> String
renderIS Nothing = "[ [\"Wanted\",\"(inconsistent)\"]," ++
                     "[\"Given\", \"(inconsistent)\"] ]"
renderIS (Just xs) = show ( [ renderWI (Given,g) | g <- given xs ] ++
                            [ renderWI (Wanted,w) | w <- wanted xs ])



--------------------------------------------------------------------------------
readMb     :: Read a => String -> Maybe a
readMb x    = readMb' reads x

readMb'    :: ReadS a -> String -> Maybe a
readMb' f x = case f x of
                [(a,"")] -> Just a
                _ -> Nothing


