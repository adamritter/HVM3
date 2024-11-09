-- //./Type.hs//
-- //./Show.hs//
-- //./Inject.hs//

module HVML.Extract where

import Control.Monad (foldM)
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
  CTR -> do
    let loc = termLoc term
    let lab = termLab term
    let cid = u12v2X lab
    let ari = u12v2Y lab
    fds <- if ari == 0
      then return []
      else mapM (\i -> got (loc + i)) [0..ari-1]
    (dups0, fds) <- foldM (\ (dups,fds) fd -> do
      (dups0, fd0) <- extractCore fd dups
      return (dups0, fds ++ [fd0])) (dups,[]) fds
    return (dups0, Ctr cid fds)
  MAT -> do
    let loc = termLoc term
    let ari = termLab term
    val <- got (loc + 0)
    css <- if ari == 0
      then return []
      else mapM (\i -> got (loc + 1 + i)) [0..ari-1]
    (dups0, val0) <- extractCore val dups
    (dups1, css0) <- foldM (\ (dups,css) cs -> do
      (dups0, cs0) <- extractCore cs dups
      return (dups0, css ++ [cs0])) (dups0,[]) css
    return (dups1, Mat val0 css0)
  REF -> do
    let loc = termLoc term
    return (dups, Ref "?" loc)
  _ -> do
    return (dups, Era)

doExtractCore :: Term -> HVM Core
doExtractCore term = do
  (_, core) <- extractCore term IS.empty
  return core
