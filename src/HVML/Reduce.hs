-- //./Type.hs//
-- //./Runtime.c//

module HVML.Reduce where

import Data.Word
import HVML.Inject
import HVML.Show
import HVML.Type
import qualified Data.Map.Strict as MS

import Debug.Trace

-- debug a b = trace a b
debug a b = b

reduce :: Book -> Term -> HVM Term
reduce book term = debug ("NEXT: " ++ termToString term) $ do
  let tag = termTag term
      lab = termLab term
      loc = termLoc term
  case tagT tag of
    APP -> do
      fun <- got (loc + 0)
      fun <- reduce book fun
      case tagT (termTag fun) of
        ERA -> reduceAppEra term fun >>= reduce book
        LAM -> reduceAppLam term fun >>= reduce book
        SUP -> reduceAppSup term fun >>= reduce book
        CTR -> reduceAppCtr term fun >>= reduce book
        W32 -> reduceAppW32 term fun >>= reduce book
        _   -> set (loc + 0) fun >> return term
    DP0 -> do
      let key = termKey term
      sub <- got key
      if termTag sub == _SUB_
        then do
          val <- got (loc + 2)
          val <- reduce book val
          case tagT (termTag val) of
            ERA -> reduceDupEra term val >>= reduce book
            LAM -> reduceDupLam term val >>= reduce book
            SUP -> reduceDupSup term val >>= reduce book
            CTR -> reduceDupCtr term val >>= reduce book
            W32 -> reduceDupW32 term val >>= reduce book
            _   -> set (loc + 2) val >> return term
        else do
          reduce book sub
    DP1 -> do
      let key = termKey term
      sub <- got key
      if termTag sub == _SUB_
        then do
          val <- got (loc + 2)
          val <- reduce book val
          case tagT (termTag val) of
            ERA -> reduceDupEra term val >>= reduce book
            LAM -> reduceDupLam term val >>= reduce book
            SUP -> reduceDupSup term val >>= reduce book
            CTR -> reduceDupCtr term val >>= reduce book
            W32 -> reduceDupW32 term val >>= reduce book
            _   -> set (loc + 2) val >> return term
        else do
          reduce book sub
    MAT -> do
      val <- got (loc + 0)
      val <- reduce book val
      case tagT (termTag val) of
        ERA -> reduceMatEra term val >>= reduce book
        LAM -> reduceMatLam term val >>= reduce book
        SUP -> reduceMatSup term val >>= reduce book
        CTR -> reduceMatCtr term val >>= reduce book
        W32 -> reduceMatW32 term val >>= reduce book
        _   -> set (loc + 0) val >> return term
    OPX -> do
      val <- got (loc + 0)
      val <- reduce book val
      case tagT (termTag val) of
        ERA -> reduceOpxEra term val >>= reduce book
        LAM -> reduceOpxLam term val >>= reduce book
        SUP -> reduceOpxSup term val >>= reduce book
        CTR -> reduceOpxCtr term val >>= reduce book
        W32 -> reduceOpxW32 term val >>= reduce book
        _   -> set (loc + 0) val >> return term
    OPY -> do
      val <- got (loc + 1)
      val <- reduce book val
      case tagT (termTag val) of
        ERA -> reduceOpyEra term val >>= reduce book
        LAM -> reduceOpyLam term val >>= reduce book
        SUP -> reduceOpySup term val >>= reduce book
        CTR -> reduceOpyCtr term val >>= reduce book
        W32 -> reduceOpyW32 term val >>= reduce book
        _   -> set (loc + 1) val >> return term
    VAR -> do
      sub <- got (loc + 0)
      if termTag sub == _SUB_
        then return $ term
        else reduce book sub
    REF -> do
      let fid = termLoc term
      case MS.lookup fid (idToCore book) of
        Just core -> do
          core <- doInjectCore book core
          reduce book core
        Nothing -> return term
    _ -> return term

normalizer :: (Book -> Term -> HVM Term) -> Book -> Term -> HVM Term
normalizer reducer book term = debug ("NORM: " ++ termToString term) $ do
  wnf <- reducer book term
  let tag = termTag wnf
      lab = termLab wnf
      loc = termLoc wnf
  case tagT tag of
    APP -> do
      fun <- got (loc + 0)
      arg <- got (loc + 1)
      fun <- normalizer reducer book fun
      arg <- normalizer reducer book arg
      set (loc + 0) fun
      set (loc + 1) arg
      return wnf
    LAM -> do
      bod <- got (loc + 1)
      bod <- normalizer reducer book bod
      set (loc + 1) bod
      return wnf
    SUP -> do
      tm0 <- got (loc + 0)
      tm1 <- got (loc + 1)
      tm0 <- normalizer reducer book tm0
      tm1 <- normalizer reducer book tm1
      set (loc + 0) tm0
      set (loc + 1) tm1
      return wnf
    DP0 -> do
      val <- got (loc + 2)
      val <- normalizer reducer book val
      set (loc + 2) val
      return wnf
    DP1 -> do
      val <- got (loc + 2)
      val <- normalizer reducer book val
      set (loc + 2) val
      return wnf
    CTR -> do
      let cid = u12v2X lab
      let ari = u12v2Y lab
      args <- mapM (\i -> got (loc + i)) (if ari == 0 then [] else [0 .. ari - 1])
      args <- mapM (normalizer reducer book) args
      mapM_ (\ (i, arg) -> set (loc + i) arg) $ zip [0..] args
      return wnf
    MAT -> do
      let ari = lab
      args <- mapM (\i -> got (loc + i)) [0 .. ari]
      args <- mapM (normalizer reducer book) args
      mapM_ (\ (i, arg) -> set (loc + i) arg) $ zip [0..] args
      return wnf
    _ -> do
      return wnf

normal :: Book -> Term -> HVM Term
normal = normalizer reduce

normalC :: Book -> Term -> HVM Term
normalC = normalizer (\ book -> reduceC)
