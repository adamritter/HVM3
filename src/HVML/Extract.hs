-- //./Type.hs//
-- //./Inject.hs//

module HVML.Extract where

import Control.Monad (foldM)
import Control.Monad.State
import Data.Char (chr, ord)
import Data.Word
import HVML.Type
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as MS

type ExtractM a = StateT (IS.IntSet, MS.Map Loc String) HVM a

extractCore :: Term -> ExtractM Core
extractCore term = case tagT (termTag term) of
  ERA -> do
    return Era

  LET -> do
    let loc = termLoc term
    let mode = modeT (termLab term)
    val <- lift $ got (loc + 1)
    bod <- lift $ got (loc + 2)
    name <- genName (loc + 0)
    val0 <- extractCore val
    bod0 <- extractCore bod
    return $ Let mode name val0 bod0
  
  LAM -> do
    let loc = termLoc term
    bod <- lift $ got (loc + 1)
    name <- genName (loc + 0)
    bod0 <- extractCore bod
    return $ Lam name bod0
    
  APP -> do
    let loc = termLoc term
    fun <- lift $ got (loc + 0)
    arg <- lift $ got (loc + 1)
    fun0 <- extractCore fun
    arg0 <- extractCore arg
    return $ App fun0 arg0
    
  SUP -> do
    let loc = termLoc term
    let lab = termLab term
    tm0 <- lift $ got (loc + 0)
    tm1 <- lift $ got (loc + 1)
    tm00 <- extractCore tm0
    tm10 <- extractCore tm1
    return $ Sup lab tm00 tm10
    
  VAR -> do
    let key = termKey term
    sub <- lift $ got key
    if termTag sub == _SUB_
    then do
      name <- genName key
      return $ Var name
    else extractCore sub
      
  DP0 -> do
    let loc = termLoc term
    let lab = termLab term
    let key = termKey term
    sub <- lift $ got key
    if termTag sub == _SUB_
    then do
      (dups, nameMap) <- get
      if IS.member (fromIntegral loc) dups
      then do
        name <- genName key
        return $ Var name
      else do
        dp0 <- genName (loc + 0)
        dp1 <- genName (loc + 1)
        val <- lift $ got (loc + 2)
        put (IS.insert (fromIntegral loc) dups, nameMap)
        val0 <- extractCore val
        return $ Dup lab dp0 dp1 val0 (Var dp0)
    else extractCore sub
      
  DP1 -> do
    let loc = termLoc term
    let lab = termLab term
    let key = termKey term
    sub <- lift $ got key
    if termTag sub == _SUB_
    then do
      (dups, nameMap) <- get
      if IS.member (fromIntegral loc) dups
      then do
        name <- genName key
        return $ Var name
      else do
        dp0 <- genName (loc + 0)
        dp1 <- genName (loc + 1)
        val <- lift $ got (loc + 2)
        put (IS.insert (fromIntegral loc) dups, nameMap)
        val0 <- extractCore val
        return $ Dup lab dp0 dp1 val0 (Var dp1)
    else extractCore sub
      
  CTR -> do
    let loc = termLoc term
    let lab = termLab term
    let cid = u12v2X lab
    let ari = u12v2Y lab
    fds <- if ari == 0
      then return []
      else lift $ mapM (\i -> got (loc + i)) [0..ari-1]
    fds0 <- mapM extractCore fds
    return $ Ctr cid fds0
    
  MAT -> do
    let loc = termLoc term
    let len = termLab term
    val <- lift $ got (loc + 0)
    css <- if len == 0
      then return []
      else lift $ mapM (\i -> got (loc + 1 + i)) [0..len-1]
    val0 <- extractCore val
    css0 <- mapM extractCore css
    css1 <- mapM (\ cs -> return (0, cs)) css0 -- NOTE: case arity lost on extraction
    return $ Mat val0 css1
    
  W32 -> do
    let val = termLoc term
    return $ U32 (fromIntegral val)
    
  OPX -> do
    let loc = termLoc term
    let opr = toEnum (fromIntegral (termLab term))
    nm0 <- lift $ got (loc + 0)
    nm1 <- lift $ got (loc + 1)
    nm00 <- extractCore nm0
    nm10 <- extractCore nm1
    return $ Op2 opr nm00 nm10
    
  OPY -> do
    let loc = termLoc term
    let opr = toEnum (fromIntegral (termLab term))
    nm0 <- lift $ got (loc + 0)
    nm1 <- lift $ got (loc + 1)
    nm00 <- extractCore nm0
    nm10 <- extractCore nm1
    return $ Op2 opr nm00 nm10
    
  REF -> do
    let loc = termLoc term
    let lab = termLab term
    let fid = u12v2X lab
    let ari = u12v2Y lab
    arg <- if ari == 0
      then return []
      else lift $ mapM (\i -> got (loc + i)) [0..ari-1]
    arg <- mapM extractCore arg
    return $ Ref "?" fid arg
    
  _ -> return Era

doExtractCore :: Term -> HVM Core
doExtractCore term = evalStateT (extractCore term) (IS.empty, MS.empty)

genName :: Loc -> ExtractM String
genName loc = do
  (dups, nameMap) <- get
  case MS.lookup loc nameMap of
    Just name -> do
      return name
    Nothing -> do
      let newName = genNameFromIndex (MS.size nameMap)
      put (dups, MS.insert loc newName nameMap)
      return newName

genNameFromIndex :: Int -> String
genNameFromIndex n = go (n + 1) "" where
  go n ac | n == 0    = ac
          | otherwise = go q (chr (ord 'a' + r) : ac)
          where (q,r) = quotRem (n - 1) 26
