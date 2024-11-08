module HVML.Extract where

import HVML.Type
import qualified Data.IntSet as IS

extractCore :: Term -> IS.IntSet -> HVM (IS.IntSet, Core)
extractCore term dups = case tagT (termTag term) of
  ERA -> return (dups, Era)
  LAM -> do
    let loc = termLoc term
    bod <- got (loc + 1)
    let var = show (loc + 0)
    (dups0, bod0) <- extractCore bod dups
    return (dups0, Lam var bod0)
  APP -> do
    let loc = termLoc term
    fun <- got (loc + 0)
    arg <- got (loc + 1)
    (dups0, fun0) <- extractCore fun dups
    (dups1, arg0) <- extractCore arg dups0
    return (dups1, App fun0 arg0)
  SUP -> do
    let loc = termLoc term
    tm0 <- got (loc + 0)
    tm1 <- got (loc + 1)
    (dups0, tm00) <- extractCore tm0 dups
    (dups1, tm10) <- extractCore tm1 dups0
    return (dups1, Sup tm00 tm10)
  VAR -> do
    let key = termKey term
    sub <- got key
    if termTag sub == _SUB_
      then return (dups, Var (show key))
      else extractCore sub dups
  DP0 -> do
    let loc = termLoc term
    let key = termKey term
    sub <- got key
    if termTag sub == _SUB_
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
    let loc = termLoc term
    let key = termKey term
    sub <- got key
    if termTag sub == _SUB_
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
