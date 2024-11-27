-- //./Type.hs//
-- //./Inject.hs//

module HVML.Reduce where

import Control.Monad (when, forM)
import Data.Word
import HVML.Extract
import HVML.Inject
import HVML.Show
import HVML.Type
import System.Exit
import qualified Data.Map.Strict as MS

reduceAt :: Bool -> ReduceAt
reduceAt debug book host = do 
  term <- got host
  let tag = termTag term
  let lab = termLab term
  let loc = termLoc term
  when debug $ do
    root <- doExtractCoreAt (const got) book 0
    core <- doExtractCoreAt (const got) book host
    putStrLn $ "reduce: " ++ termToString term
    putStrLn $ "---------------- CORE: "
    putStrLn $ coreToString core
    putStrLn $ "---------------- ROOT: "
    putStrLn $ coreToString root
  case tagT tag of
    LET -> do
      case modeT lab of
        LAZY -> do
          val <- got (loc + 1)
          cont host (reduceLet term val)
        STRI -> do
          val <- reduceAt debug book (loc + 1)
          cont host (reduceLet term val)
        PARA -> do
          error "TODO"
    APP -> do
      fun <- reduceAt debug book (loc + 0)
      case tagT (termTag fun) of
        ERA -> cont host (reduceAppEra term fun)
        LAM -> cont host (reduceAppLam term fun)
        SUP -> cont host (reduceAppSup term fun)
        TYP -> cont host (reduceAppTyp term fun)
        CTR -> cont host (reduceAppCtr term fun)
        W32 -> cont host (reduceAppW32 term fun)
        CHR -> cont host (reduceAppW32 term fun)
        _   -> set (loc + 0) fun >> return term
    DP0 -> do
      sb0 <- got (loc + 0)
      sb1 <- got (loc + 1)
      if termTag sb1 == _SUB_
        then do
          val <- reduceAt debug book (loc + 0)
          case tagT (termTag val) of
            ERA -> cont host (reduceDupEra term val)
            LAM -> cont host (reduceDupLam term val)
            SUP -> cont host (reduceDupSup term val)
            TYP -> cont host (reduceDupTyp term val)
            CTR -> cont host (reduceDupCtr term val)
            W32 -> cont host (reduceDupW32 term val)
            CHR -> cont host (reduceDupW32 term val)
            _   -> set (loc + 0) val >> return term
        else do
          set host sb0
          reduceAt debug book host
    DP1 -> do
      sb0 <- got (loc + 0)
      sb1 <- got (loc + 1)
      if termTag sb1 == _SUB_
        then do
          val <- reduceAt debug book (loc + 0)
          case tagT (termTag val) of
            ERA -> cont host (reduceDupEra term val)
            LAM -> cont host (reduceDupLam term val)
            SUP -> cont host (reduceDupSup term val)
            TYP -> cont host (reduceDupTyp term val)
            CTR -> cont host (reduceDupCtr term val)
            W32 -> cont host (reduceDupW32 term val)
            CHR -> cont host (reduceDupW32 term val)
            _   -> set (loc + 0) val >> return term
        else do
          set host sb1
          reduceAt debug book host
    ANN -> do
      typ <- reduceAt debug book (loc + 1)
      case tagT (termTag typ) of
        ERA -> cont host (reduceAnnEra term typ)
        LAM -> cont host (reduceAnnLam term typ)
        SUP -> cont host (reduceAnnSup term typ)
        TYP -> cont host (reduceAnnTyp term typ)
        CTR -> cont host (reduceAnnCtr term typ)
        W32 -> cont host (reduceAnnW32 term typ)
        CHR -> cont host (reduceAnnW32 term typ)
        _   -> set (loc + 1) typ >> return term
    MAT -> do
      val <- reduceAt debug book (loc + 0)
      case tagT (termTag val) of
        ERA -> cont host (reduceMatEra term val)
        LAM -> cont host (reduceMatLam term val)
        SUP -> cont host (reduceMatSup term val)
        TYP -> cont host (reduceMatTyp term val)
        CTR -> cont host (reduceMatCtr term val)
        W32 -> cont host (reduceMatW32 term val)
        CHR -> cont host (reduceMatW32 term val)
        _   -> set (loc + 0) val >> return term
    OPX -> do
      val <- reduceAt debug book (loc + 0)
      case tagT (termTag val) of
        ERA -> cont host (reduceOpxEra term val)
        LAM -> cont host (reduceOpxLam term val)
        SUP -> cont host (reduceOpxSup term val)
        TYP -> cont host (reduceOpxTyp term val)
        CTR -> cont host (reduceOpxCtr term val)
        W32 -> cont host (reduceOpxW32 term val)
        CHR -> cont host (reduceOpxW32 term val)
        _   -> set (loc + 0) val >> return term
    OPY -> do
      val <- reduceAt debug book (loc + 1)
      case tagT (termTag val) of
        ERA -> cont host (reduceOpyEra term val)
        LAM -> cont host (reduceOpyLam term val)
        SUP -> cont host (reduceOpySup term val)
        TYP -> cont host (reduceOpyTyp term val)
        CTR -> cont host (reduceOpyCtr term val)
        W32 -> cont host (reduceOpyW32 term val)
        CHR -> cont host (reduceOpyW32 term val)
        _   -> set (loc + 1) val >> return term
    VAR -> do
      sub <- got (loc + 0)
      if termTag sub == _SUB_
        then return term
        else do
          set host sub
          reduceAt debug book host
    REF -> do
      reduceRefAt book host
      reduceAt debug book host
    -- REF -> do
      -- let fid = u12v2X lab
      -- let ari = u12v2Y lab
      -- case MS.lookup fid (idToFunc book) of
        -- Just (nams, core) -> do
          -- incItr
          -- when (length nams /= fromIntegral ari) $ do
            -- putStrLn $ "RUNTIME_ERROR: arity mismatch on call to '@" ++ mget (idToName book) fid ++ "'."
            -- exitFailure
          -- args <- if ari == 0
            -- then return []
            -- else mapM (\i -> got (loc + i)) [0 .. ari - 1]
          -- doInjectCoreAt book core host $ zip nams args
          -- reduceAt debug book host
        -- Nothing -> return term
    otherwise -> do
      return term
  where
    cont host action = do
      ret <- action
      set host ret
      reduceAt debug book host

reduceRefAt :: Book -> Loc -> HVM Term
reduceRefAt book host = do
  term <- got host
  let lab = termLab term
  let loc = termLoc term
  let fid = u12v2X lab
  let ari = u12v2Y lab
  case fid of
    x | x == _SUP_F_ -> reduceRefAt_Sup book host loc ari
    x | x == _DUP_F_ -> reduceRefAt_Dup book host loc ari
    otherwise -> case MS.lookup fid (idToFunc book) of
      Just (nams, core) -> do
        incItr
        when (length nams /= fromIntegral ari) $ do
          putStrLn $ "RUNTIME_ERROR: arity mismatch on call to '@" ++ mget (idToName book) fid ++ "'."
          exitFailure
        args <- if ari == 0
          then return []
          else mapM (\i -> got (loc + i)) [0 .. ari - 1]
        doInjectCoreAt book core host $ zip nams args
      Nothing -> return term

-- Primitive: Dynamic Sup `@SUP(lab tm0 tm1)`
reduceRefAt_Sup :: Book -> Loc -> Loc -> Word64 -> HVM Term
reduceRefAt_Sup book host loc ari = do
  incItr
  when (ari /= 3) $ do
    putStrLn $ "RUNTIME_ERROR: arity mismatch on call to '@SUP'."
    exitFailure
  lab <- reduceAt False book (loc + 0)
  tm0 <- got (loc + 1)
  tm1 <- got (loc + 2)
  sup <- allocNode 2
  case tagT (termTag lab) of
    W32 -> do
      let ret = termNew _SUP_ (termLoc lab) sup
      set (sup + 0) tm0
      set (sup + 1) tm1
      set host ret
      return ret
    _ -> error "RUNTIME_ERROR: dynamic SUP without numeric label."

-- Primitive: Dynamic Dup `@DUP(lab val λdp0λdp1(bod))`
reduceRefAt_Dup :: Book -> Loc -> Loc -> Word64 -> HVM Term  
reduceRefAt_Dup book host loc ari = do
  incItr
  when (ari /= 3) $ do
    putStrLn $ "RUNTIME_ERROR: arity mismatch on call to '@DUP'."
    exitFailure
  lab <- reduceAt False book (loc + 0)
  val <- got (loc + 1)
  bod <- got (loc + 2)
  dup <- allocNode 2
  case tagT (termTag lab) of
    W32 -> do
      -- Create the DUP node with value and SUB
      set (dup + 0) val
      set (dup + 1) (termNew _SUB_ 0 0)
      -- Create first APP node for (APP bod DP0)
      app1 <- allocNode 2
      set (app1 + 0) bod
      set (app1 + 1) (termNew _DP0_ (termLoc lab) dup)
      -- Create second APP node for (APP (APP bod DP0) DP1)
      app2 <- allocNode 2
      set (app2 + 0) (termNew _APP_ 0 app1)
      set (app2 + 1) (termNew _DP1_ (termLoc lab) dup)
      let ret = termNew _APP_ 0 app2
      set host ret
      return ret
    _ -> error "RUNTIME_ERROR: dynamic DUP without numeric label."

reduceCAt :: Bool -> ReduceAt
reduceCAt = \ _ _ host -> do
  term <- got host
  whnf <- reduceC term
  set host whnf
  return $ whnf

-- normalAtWith :: (Book -> Term -> HVM Term) -> Book -> Loc -> HVM Term
-- normalAtWith reduceAt book host = do
  -- term <- got host
  -- if termBit term == 1 then do
    -- return term
  -- else do
    -- whnf <- reduceAt book host
    -- set host $ termSetBit whnf
    -- let tag = termTag whnf
    -- let lab = termLab whnf
    -- let loc = termLoc whnf
    -- case tagT tag of
      -- APP -> do
        -- normalAtWith reduceAt book (loc + 0)
        -- normalAtWith reduceAt book (loc + 1)
        -- return whnf
      -- LAM -> do
        -- normalAtWith reduceAt book (loc + 1)
        -- return whnf
      -- SUP -> do
        -- normalAtWith reduceAt book (loc + 0)
        -- normalAtWith reduceAt book (loc + 1)
        -- return whnf
      -- DP0 -> do
        -- normalAtWith reduceAt book (loc + 0)
        -- return whnf
      -- DP1 -> do
        -- normalAtWith reduceAt book (loc + 0)
        -- return whnf
      -- CTR -> do
        -- let ari = u12v2Y lab
        -- let ars = (if ari == 0 then [] else [0 .. ari - 1]) :: [Word64]
        -- mapM_ (\i -> normalAtWith reduceAt book (loc + i)) ars
        -- return whnf
      -- MAT -> do
        -- let ari = lab
        -- let ars = [0 .. ari] :: [Word64]
        -- mapM_ (\i -> normalAtWith reduceAt book (loc + i)) ars
        -- return whnf
      -- _ -> do
        -- return whnf

-- normalAt :: Book -> Loc -> HVM Term
-- normalAt = normalAtWith (reduceAt False)

-- normalCAt :: Book -> Loc -> HVM Term
-- normalCAt = normalAtWith (reduceCAt False)
