-- //./Type.hs//

module HVML.Reduce where

import Control.Monad (when, forM)
import Data.Word
import HVML.Extract
import HVML.Inject
import HVML.Show
import HVML.Type
import System.Exit
import qualified Data.Map.Strict as MS

reduceAt :: ReduceAt
reduceAt book host = do 
  let debug = False
  term <- got host
  let tag = termTag term
  let lab = termLab term
  let loc = termLoc term
  when debug $ do
    root <- doExtractCoreAt reduceAt book 0
    core <- doExtractCoreAt reduceAt book host
    -- putStrLn $ "---------------- CORE: "
    -- putStrLn $ coreToString core
    putStrLn $ "---------------- ROOT: "
    putStrLn $ coreToString root
    putStrLn $ "reduce " ++ termToString term
    val <- got (loc + 2)
    putStrLn $ "TERM: " ++ termToString term ++ " || VAL " ++ termToString val ++ " !!"
  case tagT tag of
    LET -> do
      case modeT lab of
        LAZY -> do
          val <- got (loc + 1)
          cont host (reduceLet term val)
        STRI -> do
          val <- reduceAt book (loc + 1)
          cont host (reduceLet term val)
        PARA -> do
          error "TODO"
    APP -> do
      fun <- reduceAt book (loc + 0)
      case tagT (termTag fun) of
        ERA -> cont host (reduceAppEra term fun)
        LAM -> cont host (reduceAppLam term fun)
        SUP -> cont host (reduceAppSup term fun)
        CTR -> cont host (reduceAppCtr term fun)
        W32 -> cont host (reduceAppW32 term fun)
        _   -> set (loc + 0) fun >> return term
    DP0 -> do
      let key = termKey term
      sub <- got key
      if termTag sub == _SUB_
        then do
          val <- reduceAt book (loc + 2)
          case tagT (termTag val) of
            ERA -> cont host (reduceDupEra term val)
            LAM -> cont host (reduceDupLam term val)
            SUP -> cont host (reduceDupSup term val)
            CTR -> cont host (reduceDupCtr term val)
            W32 -> cont host (reduceDupW32 term val)
            _   -> set (loc + 2) val >> return term
        else do
          set host sub
          reduceAt book host
    DP1 -> do
      let key = termKey term
      sub <- got key
      if termTag sub == _SUB_
        then do
          val <- reduceAt book (loc + 2)
          case tagT (termTag val) of
            ERA -> cont host (reduceDupEra term val)
            LAM -> cont host (reduceDupLam term val)
            SUP -> cont host (reduceDupSup term val)
            CTR -> cont host (reduceDupCtr term val)
            W32 -> cont host (reduceDupW32 term val)
            _   -> set (loc + 2) val >> return term
        else do
          set host sub
          reduceAt book host
    MAT -> do
      val <- reduceAt book (loc + 0)
      case tagT (termTag val) of
        ERA -> cont host (reduceMatEra term val)
        LAM -> cont host (reduceMatLam term val)
        SUP -> cont host (reduceMatSup term val)
        CTR -> cont host (reduceMatCtr term val)
        W32 -> cont host (reduceMatW32 term val)
        _   -> set (loc + 0) val >> return term
    OPX -> do
      val <- reduceAt book (loc + 0)
      case tagT (termTag val) of
        ERA -> cont host (reduceOpxEra term val)
        LAM -> cont host (reduceOpxLam term val)
        SUP -> cont host (reduceOpxSup term val)
        CTR -> cont host (reduceOpxCtr term val)
        W32 -> cont host (reduceOpxW32 term val)
        _   -> set (loc + 0) val >> return term
    OPY -> do
      val <- reduceAt book (loc + 1)
      case tagT (termTag val) of
        ERA -> cont host (reduceOpyEra term val)
        LAM -> cont host (reduceOpyLam term val)
        SUP -> cont host (reduceOpySup term val)
        CTR -> cont host (reduceOpyCtr term val)
        W32 -> cont host (reduceOpyW32 term val)
        _   -> set (loc + 1) val >> return term
    VAR -> do
      sub <- got (loc + 0)
      if termTag sub == _SUB_
        then return term
        else do
          set host sub
          reduceAt book host
    REF -> do
      let fid = u12v2X lab
      let ari = u12v2Y lab
      case MS.lookup fid (idToFunc book) of
        Just (nams, core) -> do
          incItr
          when (length nams /= fromIntegral ari) $ do
            putStrLn $ "RUNTIME_ERROR: arity mismatch on call to '@" ++ idToName book MS.! fid ++ "'."
            exitFailure
          args <- if ari == 0
            then return []
            else mapM (\i -> got (loc + i)) [0 .. ari - 1]
          doInjectCoreAt book core host $ zip nams args
          reduceAt book host
        Nothing -> return term
    otherwise -> do
      return term
  where
    cont host action = do
      ret <- action
      set host ret
      reduceAt book host

reduceCAt :: ReduceAt
reduceCAt = \ _ host -> do
  term <- got host
  whnf <- reduceC term
  set host whnf
  return $ whnf

normalAtWith :: (Book -> Term -> HVM Term) -> Book -> Loc -> HVM Term
normalAtWith reduceAt book host = do
  term <- got host
  if termBit term == 1 then do
    return term
  else do
    whnf <- reduceAt book host
    set host $ termSetBit whnf
    let tag = termTag whnf
    let lab = termLab whnf
    let loc = termLoc whnf
    case tagT tag of
      APP -> do
        normalAtWith reduceAt book (loc + 0)
        normalAtWith reduceAt book (loc + 1)
        return whnf
      LAM -> do
        normalAtWith reduceAt book (loc + 1)
        return whnf
      SUP -> do
        normalAtWith reduceAt book (loc + 0)
        normalAtWith reduceAt book (loc + 1)
        return whnf
      DP0 -> do
        normalAtWith reduceAt book (loc + 2)
        return whnf
      DP1 -> do
        normalAtWith reduceAt book (loc + 2)
        return whnf
      CTR -> do
        let ari = u12v2Y lab
        let ars = (if ari == 0 then [] else [0 .. ari - 1]) :: [Word64]
        mapM_ (\i -> normalAtWith reduceAt book (loc + i)) ars
        return whnf
      MAT -> do
        let ari = lab
        let ars = [0 .. ari] :: [Word64]
        mapM_ (\i -> normalAtWith reduceAt book (loc + i)) ars
        return whnf
      _ -> do
        return whnf

normalAt :: Book -> Loc -> HVM Term
normalAt = normalAtWith reduceAt

normalCAt :: Book -> Loc -> HVM Term
normalCAt = normalAtWith reduceCAt
