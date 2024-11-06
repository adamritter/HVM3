{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-all #-}

module Main where

-- TASK: translate HVM.kind to Haskell.
-- follow the exact same order of functions.
-- both files must display identical behavior.
-- do NOT use the ' character on variable names.
-- use numbers instead (var0, var1, etc.)
-- do it now:

import Data.Bits
import Data.Char (intToDigit)
import Data.Hashable
import Data.IORef
import Data.Word
import Numeric (showIntAtBase)
import Text.Parsec hiding (State)
import Text.Parsec.String
import qualified Data.IntSet as IS
import qualified Data.HashMap.Strict as HM
import System.CPUTime

import Debug.Trace

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

data TAG = AIR | SUB | VAR | DP0 | DP1 | APP | ERA | LAM | SUP
  deriving (Eq, Show)

tagT :: Tag -> TAG
tagT 0x00 = AIR
tagT 0x01 = SUB
tagT 0x02 = VAR
tagT 0x03 = DP0
tagT 0x04 = DP1
tagT 0x05 = APP
tagT 0x06 = ERA
tagT 0x07 = LAM
tagT 0x08 = SUP
tagT _    = error "Invalid tag"

data Heap = Heap 
  { mem :: IORef (HM.HashMap Word64 Term)
  , ini :: IORef Word64
  , end :: IORef Word64
  , itr :: IORef Word64
  }

type HVM = IO

-- Constants
-- ---------

_AIR_, _SUB_, _VAR_, _DP0_, _DP1_, _APP_, _ERA_, _LAM_, _SUP_ :: Tag
_AIR_ = 0x00
_SUB_ = 0x01
_VAR_ = 0x02
_DP0_ = 0x03
_DP1_ = 0x04
_APP_ = 0x05
_ERA_ = 0x06
_LAM_ = 0x07
_SUP_ = 0x08

_VOID_ :: Term
_VOID_ = 0x00000000000000

-- Initialization
-- --------------

newHeap :: IO Heap
newHeap = Heap <$> newIORef HM.empty <*> newIORef 0 <*> newIORef 1 <*> newIORef 0

newTerm :: Tag -> Lab -> Loc -> Term
newTerm tag lab loc = 

  let tagEnc = tag
      labEnc = shiftL lab 8
      locEnc = shiftL loc 32
  in tagEnc .|. labEnc .|. locEnc

getTag :: Term -> Tag
getTag x = x .&. 0xFF

getLab :: Term -> Lab
getLab x = (shiftR x 8) .&. 0xFFFFFF

getLoc :: Term -> Loc
getLoc x = (shiftR x 32) .&. 0xFFFFFFFF

getKey :: Term -> Loc
getKey term = case tagT (getTag term) of
  VAR -> getLoc term + 0
  DP0 -> getLoc term + 0 
  DP1 -> getLoc term + 1
  _   -> 0

tagEq :: Tag -> Tag -> Bool
tagEq x y = x == y

getIni :: Heap -> HVM Word64
getIni heap = readIORef (ini heap)

getEnd :: Heap -> HVM Word64 
getEnd heap = readIORef (end heap)

getMem :: Heap -> HVM (HM.HashMap Word64 Term)
getMem heap = readIORef (mem heap)

getItr :: Heap -> HVM Word64
getItr heap = readIORef (itr heap)

-- Memory
-- ------

swap :: Heap -> Loc -> Term -> HVM Term
swap heap loc term = do
  memRef <- readIORef (mem heap)
  let oldTerm = HM.lookupDefault 0 loc memRef
  writeIORef (mem heap) (HM.insert loc term memRef)
  return oldTerm

got :: Heap -> Word64 -> HVM Term
got heap loc = do
  memRef <- readIORef (mem heap)
  return $ HM.lookupDefault 0 loc memRef

set :: Heap -> Word64 -> Term -> HVM ()
set heap loc term = do
  _ <- swap heap loc term
  return ()

take :: Heap -> Word64 -> HVM Term
take heap loc = swap heap loc _VOID_

just :: Word64 -> HVM Word64
just = return

-- Allocation
-- ----------

allocNode :: Heap -> Word64 -> HVM Word64
allocNode heap arity = do
  endRef <- readIORef (end heap)
  writeIORef (end heap) (endRef + arity)
  return endRef

incItr :: Heap -> HVM Word64
incItr heap = do
  itrRef <- readIORef (itr heap)
  writeIORef (itr heap) (itrRef + 1)
  readIORef (end heap)

-- Injection
-- ---------

type VarMap = HM.HashMap String (Maybe Term)

hmSwap :: (Eq k, Hashable k) => k -> v -> HM.HashMap k v -> (Maybe v, HM.HashMap k v)
hmSwap k v m = 
  let old = HM.lookup k m
      new = HM.insert k v m
  in (old, new)

injectBind :: Heap -> String -> Term -> VarMap -> HVM VarMap
injectBind heap nam var vars = do
  let subKey = getKey var
  let (varLoc, vars') = hmSwap nam (Just var) vars
  case varLoc of
    Nothing -> do
      set heap subKey (newTerm _SUB_ 0 0)
      return vars'
    Just (Just oldVarLoc) -> do
      set heap oldVarLoc var
      set heap subKey (newTerm _SUB_ 0 0)
      return vars'
    Just Nothing -> do
      set heap subKey (newTerm _SUB_ 0 0)
      return vars'

injectCore :: Heap -> Core -> Word64 -> VarMap -> HVM VarMap
injectCore heap Era loc vars = do
  set heap loc (newTerm _ERA_ 0 0)
  return vars
injectCore heap (Lam vr0 bod) loc vars = do
  lam   <- allocNode heap 2
  vars0 <- injectBind heap vr0 (newTerm _VAR_ 0 (lam + 0)) vars
  vars1 <- injectCore heap bod (lam + 1) vars0
  set heap loc (newTerm _LAM_ 0 lam)
  return vars1
injectCore heap (App fun arg) loc vars = do
  app   <- allocNode heap 2
  vars0 <- injectCore heap fun (app + 0) vars
  vars1 <- injectCore heap arg (app + 1) vars0
  set heap loc (newTerm _APP_ 0 app)
  return vars1
injectCore heap (Sup tm0 tm1) loc vars = do
  sup   <- allocNode heap 2
  vars0 <- injectCore heap tm0 (sup + 0) vars
  vars1 <- injectCore heap tm1 (sup + 1) vars0
  set heap loc (newTerm _SUP_ 0 sup)
  return vars1
injectCore heap (Dup dp0 dp1 val bod) loc vars = do
  dup   <- allocNode heap 3
  vars0 <- injectBind heap dp0 (newTerm _DP0_ 0 dup) vars
  vars1 <- injectBind heap dp1 (newTerm _DP1_ 0 dup) vars0
  vars2 <- injectCore heap val (dup + 2) vars1
  injectCore heap bod loc vars2
injectCore heap (Var uid) loc vars = do
  let (var, vars') = hmSwap uid (Just loc) vars
  case var of
    Nothing -> return vars'
    Just (Just oldVar) -> do
      set heap loc oldVar
      return vars'
    Just Nothing -> return vars'

doInjectCore :: Heap -> Core -> HVM Term
doInjectCore heap core = do
  injectCore heap core 0 HM.empty
  got heap 0

extractCore :: Heap -> Term -> IS.IntSet -> HVM (IS.IntSet, Core)
extractCore heap term dups = case tagT (getTag term) of
  ERA -> return (dups, Era)
  LAM -> do
    let loc = getLoc term
    bod <- got heap (loc + 1)
    let var = show (loc + 0)
    (dups0, bod0) <- extractCore heap bod dups
    return (dups0, Lam var bod0)
  APP -> do
    let loc = getLoc term
    fun <- got heap (loc + 0)
    arg <- got heap (loc + 1)
    (dups0, fun0) <- extractCore heap fun dups
    (dups1, arg0) <- extractCore heap arg dups0
    return (dups1, App fun0 arg0)
  SUP -> do
    let loc = getLoc term
    tm0 <- got heap (loc + 0)
    tm1 <- got heap (loc + 1)
    (dups0, tm00) <- extractCore heap tm0 dups
    (dups1, tm10) <- extractCore heap tm1 dups0
    return (dups1, Sup tm00 tm10)
  VAR -> do
    let key = getKey term
    sub <- got heap key
    if tagEq (getTag sub) _SUB_
      then return (dups, Var (show key))
      else extractCore heap sub dups
  DP0 -> do
    let loc = getLoc term
    let key = getKey term
    sub <- got heap key
    if tagEq (getTag sub) _SUB_
      then if IS.member (fromIntegral loc) dups
        then return (dups, Var (show key))
        else do
          let dp0 = show (loc + 0)
          let dp1 = show (loc + 1)
          val <- got heap (loc + 2)
          (dups0, val0) <- extractCore heap val (IS.insert (fromIntegral loc) dups)
          return (dups0, Dup dp0 dp1 val0 (Var dp0))
      else extractCore heap sub dups
  DP1 -> do
    let loc = getLoc term
    let key = getKey term
    sub <- got heap key
    if tagEq (getTag sub) _SUB_
      then if IS.member (fromIntegral loc) dups
        then return (dups, Var (show key))
        else do
          let dp0 = show (loc + 0)
          let dp1 = show (loc + 1)
          val <- got heap (loc + 2)
          (dups0, val0) <- extractCore heap val (IS.insert (fromIntegral loc) dups)
          return (dups0, Dup dp0 dp1 val0 (Var dp1))
      else extractCore heap sub dups
  _ -> return (dups, Era)

doExtractCore :: Heap -> Term -> HVM Core
doExtractCore heap term = do
  (_, core) <- extractCore heap term IS.empty
  return core

-- Dumping
-- -------

dumpHeapRange :: Heap -> Word64 -> Word64 -> HVM [(Word64, Term)]
dumpHeapRange heap ini end =
  if ini < end
    then do
      head <- got heap ini
      tail <- dumpHeapRange heap (ini + 1) end
      if head == 0
        then return tail
        else return ((ini, head) : tail)
    else return []

dumpHeap :: Heap -> HVM ([(Word64, Term)], Word64, Word64, Word64)
dumpHeap heap = do
  ini <- getIni heap
  end <- getEnd heap
  itr <- getItr heap
  terms <- dumpHeapRange heap ini end
  return (terms, ini, end, itr)

-- Parsing
-- -------

parseCore :: Parser Core
parseCore = do
  spaces
  head <- lookAhead anyChar
  case head of
    '*' -> do
      string "*"
      return Era
    'λ' -> do
      char 'λ'
      vr0 <- parseName
      spaces
      bod <- parseCore
      return $ Lam vr0 bod
    '(' -> do
      char '('
      fun <- parseCore
      spaces
      arg <- parseCore
      spaces
      char ')'
      return $ App fun arg
    '{' -> do
      char '{'
      tm0 <- parseCore
      spaces
      tm1 <- parseCore
      spaces
      char '}'
      return $ Sup tm0 tm1
    '&' -> do
      string "&"
      spaces
      char '{'
      dp0 <- parseName
      spaces
      dp1 <- parseName
      spaces
      char '}'
      spaces
      char '='
      spaces
      val <- parseCore
      spaces
      bod <- parseCore
      return $ Dup dp0 dp1 val bod
    _ -> do
      name <- parseName
      return $ Var name

parseName :: Parser String
parseName = many1 (alphaNum <|> char '_')

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

heapToString :: ([(Word64, Term)], Word64, Word64, Word64) -> String
heapToString (terms, ini, end, itr) = 
  "set_ini(heap, 0x" ++ padLeft (showHex ini) 9 '0' ++ ");\n" ++
  "set_end(heap, 0x" ++ padLeft (showHex end) 9 '0' ++ ");\n" ++
  "set_itr(heap, 0x" ++ padLeft (showHex itr) 9 '0' ++ ");\n" ++
  foldr (\(k,v) txt ->
    let addr = padLeft (showHex k) 9 '0'
        term = termToString v
    in "set(heap, 0x" ++ addr ++ ", " ++ term ++ ");\n" ++ txt) "" terms

-- Helper functions

padLeft :: String -> Int -> Char -> String
padLeft str n c = replicate (n - length str) c ++ str

showHex :: Word64 -> String
showHex x = showIntAtBase 16 intToDigit (fromIntegral x) ""

-- Evaluation
-- ----------

reduce :: Heap -> Term -> HVM Term
reduce heap term = trace ("NEXT: " ++ termToString term) $ do
  let tag = getTag term
      lab = getLab term
      loc = getLoc term
  case tagT tag of
    APP -> do
      fun <- got heap (loc + 0)
      arg <- got heap (loc + 1)
      reduceApp heap lab loc fun arg
    DP0 -> do
      let key = getKey term
      sub <- got heap key
      if tagEq (getTag sub) _SUB_
        then do
          dp0 <- got heap (loc + 0)
          dp1 <- got heap (loc + 1)
          val <- got heap (loc + 2)
          reduceDup heap 0 lab loc dp0 dp1 val
        else reduce heap sub
    DP1 -> do
      let key = getKey term
      sub <- got heap key
      if tagEq (getTag sub) _SUB_
        then do
          dp0 <- got heap (loc + 0)
          dp1 <- got heap (loc + 1)
          val <- got heap (loc + 2)
          reduceDup heap 1 lab loc dp0 dp1 val
        else reduce heap sub
    VAR -> do
      sub <- got heap (loc + 0)
      if tagEq (getTag sub) _SUB_
        then return $ newTerm (getTag term) lab loc
        else reduce heap sub
    _ -> return term

reduceApp :: Heap -> Word64 -> Word64 -> Term -> Term -> HVM Term
reduceApp heap lab loc fun arg = do
  fun <- reduce heap fun
  let funTag = getTag fun
      funLab = getLab fun
      funLoc = getLoc fun
  case tagT funTag of
    ERA -> trace "APP-ERA" $ do
      _ <- incItr heap
      return fun
    LAM -> trace "APP-LAM" $ do
      _ <- incItr heap
      bod <- got heap (funLoc + 1)
      set heap (funLoc + 0) arg
      set heap (loc + 0) 0
      set heap (loc + 1) 0
      set heap (funLoc + 1) 0
      reduce heap bod
    SUP -> trace "APP-SUP" $ do
      _ <- incItr heap
      tm0 <- got heap (funLoc + 0)
      tm1 <- got heap (funLoc + 1)
      du0 <- allocNode heap 3
      su0 <- allocNode heap 2
      ap0 <- allocNode heap 2
      ap1 <- allocNode heap 2
      set heap (du0 + 0) (newTerm _SUB_ 0 0)
      set heap (du0 + 1) (newTerm _SUB_ 0 0)
      set heap (du0 + 2) (newTerm _ERA_ 0 7)
      set heap (du0 + 2) arg
      set heap (ap0 + 0) tm0
      set heap (ap0 + 1) (newTerm _DP0_ 0 du0)
      set heap (ap1 + 0) tm1
      set heap (ap1 + 1) (newTerm _DP1_ 0 du0)
      set heap (su0 + 0) (newTerm _APP_ 0 ap0)
      set heap (su0 + 1) (newTerm _APP_ 0 ap1)
      set heap (loc + 0) 0
      set heap (loc + 1) 0
      set heap (funLoc + 0) 0
      set heap (funLoc + 1) 0
      return $ newTerm _SUP_ 0 su0
    _ -> do
      set heap (loc + 0) fun
      return $ newTerm _APP_ lab loc

reduceDup :: Heap -> Word64 -> Word64 -> Word64 -> Term -> Term -> Term -> HVM Term
reduceDup heap n lab loc dp0 dp1 val = do
  val <- reduce heap val
  let valTag = getTag val
      valLab = getLab val
      valLoc = getLoc val
  case tagT valTag of
    ERA -> trace "DUP-ERA" $ do
      _ <- incItr heap
      set heap (loc + 0) val
      set heap (loc + 1) val
      set heap (loc + 2) 0
      got heap (loc + n)
    LAM -> trace "DUP-LAM" $ do
      _ <- incItr heap
      let vr0 = valLoc + 0
      bod <- got heap (valLoc + 1)
      du0 <- allocNode heap 3
      lm0 <- allocNode heap 2
      lm1 <- allocNode heap 2
      su0 <- allocNode heap 2
      set heap (du0 + 0) (newTerm _SUB_ 0 0)
      set heap (du0 + 1) (newTerm _SUB_ 0 0)
      set heap (du0 + 2) bod
      set heap (lm0 + 0) (newTerm _SUB_ 0 0)
      set heap (lm0 + 1) (newTerm _DP0_ 0 du0)
      set heap (lm1 + 0) (newTerm _SUB_ 0 0)
      set heap (lm1 + 1) (newTerm _DP1_ 0 du0)
      set heap (su0 + 0) (newTerm _VAR_ 0 lm0)
      set heap (su0 + 1) (newTerm _VAR_ 0 lm1)
      set heap (loc + 0) (newTerm _LAM_ 0 lm0)
      set heap (loc + 1) (newTerm _LAM_ 0 lm1)
      set heap (vr0 + 0) (newTerm _SUP_ 0 su0)
      set heap (loc + 2) 0
      set heap (valLoc + 1) 0
      got heap (loc + n) >>= reduce heap
    SUP -> trace "DUP-SUP" $ do
      _ <- incItr heap
      tm0 <- got heap (valLoc + 0)
      tm1 <- got heap (valLoc + 1)
      set heap (loc + 0) tm0
      set heap (loc + 1) tm1
      set heap (loc + 2) 0
      set heap (valLoc + 0) 0
      set heap (valLoc + 1) 0
      got heap (loc + n) >>= reduce heap
    _ -> do
      set heap (loc + 2) val
      return $ newTerm (if n == 0 then _DP0_ else _DP1_) lab loc

normal :: Heap -> Term -> HVM Term
normal heap term = do
  wnf <- reduce heap term
  let tag = getTag wnf
      lab = getLab wnf
      loc = getLoc wnf
  case tagT tag of
    APP -> do
      fun <- got heap (loc + 0)
      fun <- normal heap fun
      arg <- got heap (loc + 1)
      arg <- normal heap arg
      set heap (loc + 0) fun
      set heap (loc + 1) arg
      return wnf
    LAM -> do
      bod <- got heap (loc + 1)
      bod <- normal heap bod
      set heap (loc + 1) bod
      return wnf
    SUP -> do
      tm0 <- got heap (loc + 0)
      tm1 <- got heap (loc + 1)
      tm0 <- normal heap tm0
      tm1 <- normal heap tm1
      set heap (loc + 0) tm0
      set heap (loc + 1) tm1
      return wnf
    DP0 -> do
      val <- got heap (loc + 2)
      val <- normal heap val
      set heap (loc + 2) val
      return wnf
    DP1 -> do
      val <- got heap (loc + 2)
      val <- normal heap val
      set heap (loc + 2) val
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

-- main :: IO ()
-- main = do

  -- let term = doParseCore $ unlines
        -- [ "(("
        -- , genPow2 15
        -- , "  λX ((X λT0 λF0 F0) λT1 λF1 T1))"
        -- , "  λT2 λF2 T2)"
        -- ]

  -- -- let term = doParseCore "({λx x λy y} λa a)"
  -- putStrLn "[CORE]"
  -- putStrLn $ coreToString term
  -- putStrLn $ ""

  -- heap <- newHeap
  -- root <- doInjectCore heap term
  
  -- -- putStrLn "[HEAP]"
  -- -- heap' <- dumpHeap heap
  -- -- putStrLn $ heapToString heap'
  -- putStrLn "[CORE]"
  -- core <- doExtractCore heap root
  -- putStrLn $ coreToString core
  -- putStrLn ""
  
  -- putStrLn "[Normalizing...]"
  -- norm <- normal heap root
  -- set heap 0 norm
  -- putStrLn ""
  
  -- -- putStrLn "[HEAP_NF]"
  -- -- heap'' <- dumpHeap heap
  -- -- putStrLn $ heapToString heap''
  -- putStrLn "[CORE_NF]"
  -- norm' <- doExtractCore heap norm
  -- putStrLn $ coreToString norm'
  -- putStrLn ""
  
  -- itr <- getItr heap
  -- putStrLn "[ITR]"
  -- print itr

-- TODO: rewrite main to print the time it took to normalize the term, in ms. keep all else the same. don't change anything else.
main :: IO ()
main = do
  start <- getCPUTime
  heap <- newHeap

  let term = doParseCore $ unlines
        [ "(λa * (("
        , genPow2 24
        , "  λX ((X λT0 λF0 F0) λT1 λF1 T1))"
        , "  λT2 λF2 T2))"
        ]
  -- let term = doParseCore "(λx x λy y)"

  putStrLn "[CORE]"
  putStrLn $ coreToString term
  putStrLn $ ""

  -- Inject core term
  root <- doInjectCore heap term

  putStrLn "[HEAP]"
  heap' <- dumpHeap heap
  putStrLn $ heapToString heap'
  
  putStrLn "[CORE]"
  core <- doExtractCore heap root
  putStrLn $ coreToString core
  putStrLn ""
  
  putStrLn "[Normalizing...]"
  norm <- normal heap root
  set heap 0 norm
  putStrLn ""
  
  putStrLn "[CORE_NF]"
  norm' <- doExtractCore heap norm
  putStrLn $ coreToString norm'
  putStrLn ""
  
  end <- getCPUTime
  let diff = fromIntegral (end - start) / (10^9) :: Double
  
  itr <- getItr heap
  putStrLn "[ITR]"
  print itr
  putStrLn $ "[TIME] " ++ show diff ++ "ms"
