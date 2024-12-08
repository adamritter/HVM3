module HVMS.Extract where

import Data.Word
import HVMS.Type

-- Term to Core
-- ------------

extractPCore :: Term -> IO PCore
extractPCore term = case termTag term of
  tag | tag == _NUL_ -> return PNul
      | tag == _VAR_ -> do
          got <- get (termLoc term)
          extractVar (termLoc term) got
      | tag == _LAM_ -> do
          let loc = termLoc term
          var <- get (loc + 0)
          bod <- get (loc + 1)
          var' <- extractNCore (loc + 0) var
          bod' <- extractPCore bod
          return $ PLam var' bod'
      | tag == _SUP_ -> do
          let loc = termLoc term
          tm1 <- get (loc + 0)
          tm2 <- get (loc + 1)
          tm1' <- extractPCore tm1
          tm2' <- extractPCore tm2
          return $ PSup tm1' tm2'
      | tag == _W32_ -> do
          return $ PU32 (termLoc term)
      | otherwise -> return PNul

-- Convert a term in memory to a NCore.
-- The optional location is the location of the term
-- being extracted in the buffer.
extractNCore :: Loc -> Term -> IO NCore
extractNCore loc term = case termTag term of
  tag | tag == _ERA_ -> return NEra
      | tag == _SUB_ -> return $ NSub ("v" ++ show loc)
      | tag == _APP_ -> do
          let loc = termLoc term
          arg <- get (loc + 0)
          ret <- get (loc + 1)
          arg' <- extractPCore arg
          ret' <- extractNCore (loc + 1) ret
          return $ NApp arg' ret'
      | tag == _DUP_ -> do
          let loc = termLoc term
          dp1 <- get (loc + 0)
          dp2 <- get (loc + 1)
          dp1' <- extractNCore (loc + 0) dp1
          dp2' <- extractNCore (loc + 1) dp2
          return $ NDup dp1' dp2'
      | otherwise -> return NEra

extractVar :: Loc -> Term -> IO PCore
extractVar loc term = case termTag term of
  tag | tag == _VAR_ -> extractPCore term
      | tag == _NUL_ -> extractPCore term
      | tag == _LAM_ -> extractPCore term
      | tag == _SUP_ -> extractPCore term
      | tag == _SUB_ -> return $ PVar ("v" ++ show loc)
      | tag == _W32_ -> return $ PU32 (termLoc term)
      | otherwise    -> return PNul

-- Bag and Net Extraction
-- ---------------------

extractDex :: Loc -> IO Dex
extractDex loc = do
  neg  <- get (loc + 0)
  pos  <- get (loc + 1)
  neg' <- extractNCore (loc + 0) neg
  pos' <- extractPCore pos
  return (neg', pos')

extractBag :: [Loc] -> IO Bag
extractBag [] = return []
extractBag (loc:locs) = do
  dex  <- extractDex loc
  dexs <- extractBag locs
  return (dex : dexs)

extractNet :: Term -> IO Net
extractNet root = do
  root' <- extractPCore root
  ini   <- rbagIni
  end   <- rbagEnd
  bag   <- extractBag [ini, ini+2..end-2]
  return $ Net root' bag

-- Main Entry Points
-- ----------------

doExtractNet :: Term -> IO Net
doExtractNet root = extractNet root
