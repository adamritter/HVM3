module HVMS.Extract where

import Data.Word
import HVMS.Type

-- Term to Core
-- ------------

extractPCore :: Term -> IO PCore
extractPCore term = case termTag term of
  tag | tag == _NUL_ -> return PNul
      | tag == _VAR_ -> do
          get <- get (termLoc term)
          extractVar (termLoc term) get
      | tag == _LAM_ -> do
          let loc = termLoc term
          var <- get (loc + 0)
          bod <- get (loc + 1)
          var' <- extractNCore var
          bod' <- extractPCore bod
          return $ PLam var' bod'
      | tag == _SUP_ -> do
          let loc = termLoc term
          tm1 <- get (loc + 0)
          tm2 <- get (loc + 1)
          tm1' <- extractPCore tm1
          tm2' <- extractPCore tm2
          return $ PSup tm1' tm2'
      | otherwise -> return PNul

extractNCore :: Term -> IO NCore
extractNCore term = case termTag term of
  tag | tag == _ERA_ -> return NEra
      | tag == _SUB_ -> do
          get <- get (termLoc term)
          extractSub (termLoc term) get
      | tag == _APP_ -> do
          let loc = termLoc term
          arg <- get (loc + 0)
          ret <- get (loc + 1)
          arg' <- extractPCore arg
          ret' <- extractNCore ret
          return $ NApp arg' ret'
      | tag == _DUP_ -> do
          let loc = termLoc term
          dp1 <- get (loc + 0)
          dp2 <- get (loc + 1)
          dp1' <- extractNCore dp1
          dp2' <- extractNCore dp2
          return $ NDup dp1' dp2'
      | otherwise -> return NEra

extractVar :: Loc -> Term -> IO PCore
extractVar var term = case termTag term of
  tag | tag == _VAR_ -> extractPCore term
      | tag == _NUL_ -> extractPCore term
      | tag == _LAM_ -> extractPCore term
      | tag == _SUP_ -> extractPCore term
      | tag == _SUB_ -> if termLoc term == var
                        then return $ PVar (show var)
                        else extractPCore (termNew _SUB_ 0 (termLoc term))
      | otherwise -> return PNul

extractSub :: Loc -> Term -> IO NCore
extractSub sub term = case termTag term of
  tag | tag == _VAR_ -> extractNCore term
      | tag == _ERA_ -> extractNCore term
      | tag == _APP_ -> extractNCore term
      | tag == _DUP_ -> extractNCore term
      | tag == _SUB_ -> if termLoc term == sub
                        then return $ NSub (show sub)
                        else extractNCore (termNew _SUB_ 0 (termLoc term))
      | otherwise -> return NEra

-- Bag and Net Extraction
-- ---------------------

extractDex :: (Term, Term) -> IO Dex
extractDex (neg, pos) = do
  neg' <- extractNCore neg
  pos' <- extractPCore pos
  return (neg', pos')

extractBag :: [(Word64, (Term, Term))] -> IO Bag
extractBag [] = return []
extractBag ((_, dex):dexs) = do
  dex' <- extractDex dex
  dexs' <- extractBag dexs
  return (dex' : dexs')

extractNet :: Term -> [(Word64, (Term, Term))] -> IO Net
extractNet root bag = do
  root' <- extractPCore root
  bag' <- extractBag bag
  return $ Net root' bag'

-- Main Entry Points
-- ----------------

doExtractNet :: Term -> [(Word64, (Term, Term))] -> IO Net
doExtractNet root bag = extractNet root bag
