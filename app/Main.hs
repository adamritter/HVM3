-- main.c:
-- //./main.c//

{-# OPTIONS_GHC -Wno-all #-}

module Main where

import Data.Bits
import Data.Char (intToDigit)
import Data.IORef
import Data.Word
import Foreign.Ptr
import Numeric (showIntAtBase)
import System.CPUTime
import Text.Parsec hiding (State)
import Text.Parsec.String
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS

import Debug.Trace

debug a b = b

-- Core Types
-- ----------

data Core
  = Var String
  | Era
  | Lam String Core
  | App Core Core
  | Sup Core Core
  | Dup String String Core Core
  deriving (Show, Eq)

-- Runtime Types
-- -------------

type Tag  = Word64
type Lab  = Word64
type Loc  = Word64
type Term = Word64

data TAG
  = DP0
  | DP1
  | VAR
  | APP
  | ERA
  | LAM
  | SUP
  | SUB
  deriving (Eq, Show)

type HVM = IO

-- C Functions
-- -----------

foreign import ccall unsafe "main.c hvm_init"
  hvmInit :: IO ()

foreign import ccall unsafe "main.c hvm_free"
  hvmFree :: IO ()

foreign import ccall unsafe "main.c new_term"
  newTerm :: Tag -> Lab -> Loc -> Term

foreign import ccall unsafe "main.c get_tag"
  getTag :: Term -> Tag

foreign import ccall unsafe "main.c get_lab"
  getLab :: Term -> Lab

foreign import ccall unsafe "main.c get_loc"
  getLoc :: Term -> Loc

foreign import ccall unsafe "main.c get_key"
  getKey :: Term -> Loc

foreign import ccall unsafe "main.c alloc_node"
  allocNode :: Word64 -> IO Word64

foreign import ccall unsafe "main.c set"
  set :: Word64 -> Term -> IO ()

foreign import ccall unsafe "main.c got"
  got :: Word64 -> IO Term

foreign import ccall unsafe "main.c take"
  take :: Word64 -> IO Term

foreign import ccall unsafe "main.c get_len"
  getLen :: IO Word64

foreign import ccall unsafe "main.c get_itr"
  getItr :: IO Word64

foreign import ccall unsafe "main.c inc_itr"
  incItr :: IO Word64

foreign import ccall unsafe "main.c reduce"
  reduce :: Term -> IO Term

-- Constants
-- ---------

tagT :: Tag -> TAG
tagT 0x00 = DP0
tagT 0x01 = DP1
tagT 0x02 = VAR
tagT 0x03 = APP
tagT 0x04 = ERA
tagT 0x05 = LAM
tagT 0x06 = SUP
tagT 0x07 = SUB

_DP0_, _DP1_, _VAR_, _APP_, _ERA_, _LAM_, _SUP_, _SUB_ :: Tag
_DP0_ = 0x00
_DP1_ = 0x01
_VAR_ = 0x02
_APP_ = 0x03
_ERA_ = 0x04
_LAM_ = 0x05
_SUP_ = 0x06
_SUB_ = 0x07

-- Injection
-- ---------

type VarMap = IM.IntMap (Maybe Term)

injectBind :: String -> Term -> VarMap -> HVM VarMap
injectBind nam var vars = do
  let subKey = getKey var
  let namHash = hash nam
  case IM.lookup namHash vars of
    Nothing -> do
      set subKey (newTerm _SUB_ 0 0)
      return $ IM.insert namHash (Just var) vars
    Just mOldVar -> case mOldVar of
      Nothing -> do
        set subKey (newTerm _SUB_ 0 0)
        return $ IM.insert namHash (Just var) vars
      Just oldVar -> do
        set oldVar var
        set subKey (newTerm _SUB_ 0 0)
        return $ IM.insert namHash (Just var) vars
  where
    hash :: String -> Int
    hash = foldl (\h c -> 33 * h + fromEnum c) 5381

injectCore :: Core -> Word64 -> VarMap -> HVM VarMap
injectCore Era loc vars = do
  set loc (newTerm _ERA_ 0 0)
  return vars
injectCore (Lam vr0 bod) loc vars = do
  lam   <- allocNode 2
  vars0 <- injectBind vr0 (newTerm _VAR_ 0 (lam + 0)) vars
  vars1 <- injectCore bod (lam + 1) vars0
  set loc (newTerm _LAM_ 0 lam)
  return vars1
injectCore (App fun arg) loc vars = do
  app   <- allocNode 2
  vars0 <- injectCore fun (app + 0) vars
  vars1 <- injectCore arg (app + 1) vars0
  set loc (newTerm _APP_ 0 app)
  return vars1
injectCore (Sup tm0 tm1) loc vars = do
  sup   <- allocNode 2
  vars0 <- injectCore tm0 (sup + 0) vars
  vars1 <- injectCore tm1 (sup + 1) vars0
  set loc (newTerm _SUP_ 0 sup)
  return vars1
injectCore (Dup dp0 dp1 val bod) loc vars = do
  dup   <- allocNode 3
  vars0 <- injectBind dp0 (newTerm _DP0_ 0 dup) vars
  vars1 <- injectBind dp1 (newTerm _DP1_ 0 dup) vars0
  vars2 <- injectCore val (dup + 2) vars1
  injectCore bod loc vars2
injectCore (Var uid) loc vars = do
  let namHash = hash uid
  case IM.lookup namHash vars of
    Nothing -> return $ IM.insert namHash (Just loc) vars
    Just mOldVar -> case mOldVar of
      Nothing -> return $ IM.insert namHash (Just loc) vars
      Just oldVar -> do
        set loc oldVar
        return $ IM.insert namHash (Just loc) vars
  where
    hash :: String -> Int
    hash = foldl (\h c -> 33 * h + fromEnum c) 5381

doInjectCore :: Core -> HVM Term
doInjectCore core = do
  injectCore core 0 IM.empty
  got 0

-- Extraction
-- ----------

extractCore :: Term -> IS.IntSet -> HVM (IS.IntSet, Core)
extractCore term dups = case tagT (getTag term) of
  ERA -> return (dups, Era)
  LAM -> do
    let loc = getLoc term
    bod <- got (loc + 1)
    let var = show (loc + 0)
    (dups0, bod0) <- extractCore bod dups
    return (dups0, Lam var bod0)
  APP -> do
    let loc = getLoc term
    fun <- got (loc + 0)
    arg <- got (loc + 1)
    (dups0, fun0) <- extractCore fun dups
    (dups1, arg0) <- extractCore arg dups0
    return (dups1, App fun0 arg0)
  SUP -> do
    let loc = getLoc term
    tm0 <- got (loc + 0)
    tm1 <- got (loc + 1)
    (dups0, tm00) <- extractCore tm0 dups
    (dups1, tm10) <- extractCore tm1 dups0
    return (dups1, Sup tm00 tm10)
  VAR -> do
    let key = getKey term
    sub <- got key
    if getTag sub == _SUB_
      then return (dups, Var (show key))
      else extractCore sub dups
  DP0 -> do
    let loc = getLoc term
    let key = getKey term
    sub <- got key
    if getTag sub == _SUB_
      then if IS.member (fromIntegral loc) dups
        then return (dups, Var (show key))
        else do
          let dp0 = show (loc + 0)
          let dp1 = show (loc + 1)
          val <- got (loc + 2)
          (dups0, val0) <- extractCore val (IS.insert (fromIntegral loc) dups)
          return (dups0, Dup dp0 dp1 val0 (Var dp0))
      else extractCore sub dups
  DP1 -> do
    let loc = getLoc term
    let key = getKey term
    sub <- got key
    if getTag sub == _SUB_
      then if IS.member (fromIntegral loc) dups
        then return (dups, Var (show key))
        else do
          let dp0 = show (loc + 0)
          let dp1 = show (loc + 1)
          val <- got (loc + 2)
          (dups0, val0) <- extractCore val (IS.insert (fromIntegral loc) dups)
          return (dups0, Dup dp0 dp1 val0 (Var dp1))
      else extractCore sub dups
  _ -> return (dups, Era)

doExtractCore :: Term -> HVM Core
doExtractCore term = do
  (_, core) <- extractCore term IS.empty
  return core

-- Dumping
-- -------

dumpHeapRange :: Word64 -> Word64 -> HVM [(Word64, Term)]
dumpHeapRange ini len =
  if ini < len then do
    head <- got ini
    tail <- dumpHeapRange (ini + 1) len
    if head == 0
      then return tail
      else return ((ini, head) : tail)
  else return []

dumpHeap :: HVM ([(Word64, Term)], Word64)
dumpHeap = do
  len <- getLen
  itr <- getItr
  terms <- dumpHeapRange 0 len
  return (terms, itr)

-- Parsing
-- -------

consume str = spaces >> string str

parseCore :: Parser Core
parseCore = do
  spaces
  head <- lookAhead anyChar
  case head of
    '*' -> do
      consume "*"
      return Era
    'λ' -> do
      consume "λ"
      vr0 <- parseName
      bod <- parseCore
      return $ Lam vr0 bod
    '(' -> do
      consume "("
      fun <- parseCore
      arg <- parseCore
      consume ")"
      return $ App fun arg
    '{' -> do
      consume "{"
      tm0 <- parseCore
      tm1 <- parseCore
      consume "}"
      return $ Sup tm0 tm1
    '&' -> do
      consume "&"
      consume "{"
      dp0 <- parseName
      dp1 <- parseName
      consume "}"
      consume "="
      val <- parseCore
      bod <- parseCore
      return $ Dup dp0 dp1 val bod
    _ -> do
      name <- parseName
      return $ Var name

parseName :: Parser String
parseName = spaces >> many1 (alphaNum <|> char '_')

doParseCore :: String -> Core
doParseCore code = case parse parseCore "" code of
  Right core -> core
  Left _     -> Era

-- Core Stringification
-- --------------------

coreToString :: Core -> String
coreToString (Var nam)             = nam
coreToString Era                   = "*"
coreToString (Lam vr0 bod)         = "λ" ++ vr0 ++ " " ++ coreToString bod
coreToString (App fun arg)         = "(" ++ coreToString fun ++ " " ++ coreToString arg ++ ")"
coreToString (Sup tm0 tm1)         = "{" ++ coreToString tm0 ++ " " ++ coreToString tm1 ++ "}"
coreToString (Dup dp0 dp1 val bod) = "&{" ++ dp0 ++ " " ++ dp1 ++ "} = " ++ coreToString val ++ " " ++ coreToString bod

-- Runtime Stringification
-- -----------------------

tagToString :: Tag -> String
tagToString t = show (tagT t)

labToString :: Word64 -> String
labToString loc = padLeft (showHex loc) 6 '0'

locToString :: Word64 -> String
locToString loc = padLeft (showHex loc) 9 '0'

termToString :: Term -> String
termToString term =
  let tag = tagToString (getTag term)
      lab = labToString (getLab term)
      loc = locToString (getLoc term)
  in "new_term(" ++ tag ++ ",0x" ++ lab ++ ",0x" ++ loc ++ ")"

heapToString :: ([(Word64, Term)], Word64) -> String
heapToString (terms, itr) = 
  "set_itr(0x" ++ padLeft (showHex itr) 9 '0' ++ ");\n" ++
  foldr (\(k,v) txt ->
    let addr = padLeft (showHex k) 9 '0'
        term = termToString v
    in "set(0x" ++ addr ++ ", " ++ term ++ ");\n" ++ txt) "" terms

padLeft :: String -> Int -> Char -> String
padLeft str n c = replicate (n - length str) c ++ str

showHex :: Word64 -> String
showHex x = showIntAtBase 16 intToDigit (fromIntegral x) ""

-- Normalization
-- -------------

normal :: Term -> HVM Term
normal term = do
  wnf <- reduce term
  let tag = getTag wnf
      lab = getLab wnf
      loc = getLoc wnf
  case tagT tag of
    APP -> do
      fun <- got (loc + 0)
      arg <- got (loc + 1)
      fun <- normal fun
      arg <- normal arg
      set (loc + 0) fun
      set (loc + 1) arg
      return wnf
    LAM -> do
      bod <- got (loc + 1)
      bod <- normal bod
      set (loc + 1) bod
      return wnf
    SUP -> do
      tm0 <- got (loc + 0)
      tm1 <- got (loc + 1)
      tm0 <- normal tm0
      tm1 <- normal tm1
      set (loc + 0) tm0
      set (loc + 1) tm1
      return wnf
    DP0 -> do
      val <- got (loc + 2)
      val <- normal val
      set (loc + 2) val
      return wnf
    DP1 -> do
      val <- got (loc + 2)
      val <- normal val
      set (loc + 2) val
      return wnf
    _ -> return wnf

-- Main
-- ----

genPow2 :: Int -> String
genPow2 n = 
  let pairs = [(i, j) | i <- [0..n-1], j <- ['a','b']]
      vars = [("f" ++ show i ++ [j]) | (i,j) <- pairs]
      base = "λf "
      dups = [concat [" &{f", show i, "a f", show i, "b} = ", if i == 0 then "f" else 
              concat ["λk", show i, " (f", show (i-1), "a (f", show (i-1), "b k", show i, "))"]] 
              | i <- [0..n-1]]
      final = concat ["λx (f", show (n-1), "a (f", show (n-1), "b x))"]
  in concat $ [base] ++ [concat (dups ++ [" " ++ final])]

main :: IO ()
main = do
  start <- getCPUTime
  hvmInit

  let term = doParseCore $ unlines
        [ "(("
        , genPow2 24
        , "  λX ((X λT0 λF0 F0) λT1 λF1 T1))"
        , "  λT2 λF2 T2)"
        ]
  -- let term = doParseCore "(λx x λy y)"

  putStrLn "[CORE]"
  putStrLn $ coreToString term
  putStrLn $ ""

  -- Inject core term
  root <- doInjectCore term
  -- TODO: print root

  -- putStrLn "[HEAP]"
  -- heap' <- dumpHeap
  -- putStrLn $ heapToString heap'
  
  -- putStrLn "[CORE_EX]"
  -- core <- doExtractCore root
  -- putStrLn $ coreToString core
  -- putStrLn ""
  
  putStrLn "[Normalizing...]"
  norm <- normal root
  set 0 norm
  putStrLn ""
  
  putStrLn "[CORE_NF]"
  norm' <- doExtractCore norm
  putStrLn $ coreToString norm'
  putStrLn ""
  
  end <- getCPUTime
  let diff = fromIntegral (end - start) / (10^9) :: Double
  
  itr <- getItr
  len <- getLen
  let mips = (fromIntegral itr / 1000000.0) / (diff / 1000.0)
  putStrLn $ "ITRS: " ++ show itr
  putStrLn $ "TIME: " ++ show diff ++ "ms"
  putStrLn $ "SIZE: " ++ show len
  putStrLn $ "MIPS: " ++ show mips
  
  hvmFree
