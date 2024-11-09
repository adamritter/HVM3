-- //./Runtime.c//
-- //./Type.hs//

module HVML.Normal where

import Data.Word
import HVML.Inject
import HVML.Show
import HVML.Type
import qualified Data.Map.Strict as MS

debug a b = b

reduce :: Book -> Term -> HVM Term
reduce book term = debug ("NEXT: " ++ termToString term) $ do
  let tag = termTag term
      lab = termLab term
      loc = termLoc term
  case tagT tag of
    APP -> do
      fun <- got (loc + 0)
      arg <- got (loc + 1)
      reduceApp book lab loc fun arg
    DP0 -> do
      let key = termKey term
      sub <- got key
      if termTag sub == _SUB_
        then do
          dp0 <- got (loc + 0)
          dp1 <- got (loc + 1)
          val <- got (loc + 2)
          reduceDup book 0 lab loc dp0 dp1 val
        else reduce book sub
    DP1 -> do
      let key = termKey term
      sub <- got key
      if termTag sub == _SUB_
        then do
          dp0 <- got (loc + 0)
          dp1 <- got (loc + 1)
          val <- got (loc + 2)
          reduceDup book 1 lab loc dp0 dp1 val
        else reduce book sub
    VAR -> do
      sub <- got (loc + 0)
      if termTag sub == _SUB_
        then return $ termNew (termTag term) lab loc
        else reduce book sub
    REF -> do
      let fid = termLoc term
      case MS.lookup fid (idToCore book) of
        Just core -> do
          core <- doInjectCore book core
          reduce book core
        Nothing -> return term
    _ -> return term

reduceApp :: Book -> Word64 -> Word64 -> Term -> Term -> HVM Term
reduceApp book lab loc fun arg = do
  fun <- reduce book fun
  let funTag = termTag fun
      funLab = termLab fun
      funLoc = termLoc fun
  case tagT funTag of
    ERA -> debug "APP-ERA" $ do
      incItr
      return fun
    LAM -> debug "APP-LAM" $ do
      incItr
      bod <- got (funLoc + 1)
      set (funLoc + 0) arg
      set (loc + 0) 0
      set (loc + 1) 0
      set (funLoc + 1) 0
      reduce book bod
    SUP -> debug "APP-SUP" $ do
      incItr
      tm0 <- got (funLoc + 0)
      tm1 <- got (funLoc + 1)
      du0 <- allocNode 3
      su0 <- allocNode 2
      ap0 <- allocNode 2
      ap1 <- allocNode 2
      set (du0 + 0) (termNew _SUB_ 0 0)
      set (du0 + 1) (termNew _SUB_ 0 0)
      set (du0 + 2) (termNew _ERA_ 0 7)
      set (du0 + 2) arg
      set (ap0 + 0) tm0
      set (ap0 + 1) (termNew _DP0_ 0 du0)
      set (ap1 + 0) tm1
      set (ap1 + 1) (termNew _DP1_ 0 du0)
      set (su0 + 0) (termNew _APP_ 0 ap0)
      set (su0 + 1) (termNew _APP_ 0 ap1)
      set (loc + 0) 0
      set (loc + 1) 0
      set (funLoc + 0) 0
      set (funLoc + 1) 0
      return $ termNew _SUP_ 0 su0
    _ -> do
      set (loc + 0) fun
      return $ termNew _APP_ lab loc

reduceDup :: Book -> Word64 -> Word64 -> Word64 -> Term -> Term -> Term -> HVM Term
reduceDup book n lab loc dp0 dp1 val = do
  val <- reduce book val
  let valTag = termTag val
      valLab = termLab val
      valLoc = termLoc val
  case tagT valTag of
    ERA -> debug "DUP-ERA" $ do
      incItr
      set (loc + 0) val
      set (loc + 1) val
      set (loc + 2) 0
      got (loc + n)
    LAM -> debug "DUP-LAM" $ do
      incItr
      let vr0 = valLoc + 0
      bod <- got (valLoc + 1)
      du0 <- allocNode 3
      lm0 <- allocNode 2
      lm1 <- allocNode 2
      su0 <- allocNode 2
      set (du0 + 0) (termNew _SUB_ 0 0)
      set (du0 + 1) (termNew _SUB_ 0 0)
      set (du0 + 2) bod
      set (lm0 + 0) (termNew _SUB_ 0 0)
      set (lm0 + 1) (termNew _DP0_ 0 du0)
      set (lm1 + 0) (termNew _SUB_ 0 0)
      set (lm1 + 1) (termNew _DP1_ 0 du0)
      set (su0 + 0) (termNew _VAR_ 0 lm0)
      set (su0 + 1) (termNew _VAR_ 0 lm1)
      set (loc + 0) (termNew _LAM_ 0 lm0)
      set (loc + 1) (termNew _LAM_ 0 lm1)
      set (vr0 + 0) (termNew _SUP_ 0 su0)
      set (loc + 2) 0
      set (valLoc + 1) 0
      got (loc + n) >>= reduce book
    SUP -> debug "DUP-SUP" $ do
      incItr
      tm0 <- got (valLoc + 0)
      tm1 <- got (valLoc + 1)
      set (loc + 0) tm0
      set (loc + 1) tm1
      set (loc + 2) 0
      set (valLoc + 0) 0
      set (valLoc + 1) 0
      got (loc + n) >>= reduce book
    _ -> do
      set (loc + 2) val
      return $ termNew (if n == 0 then _DP0_ else _DP1_) lab loc

normalizer :: (Book -> Term -> HVM Term) -> Book -> Term -> HVM Term
normalizer reducer book term = do
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
    _ -> do
      return wnf

normal :: Book -> Term -> HVM Term
normal = normalizer reduce

normalC :: Book -> Term -> HVM Term
normalC = normalizer (\ book -> reduceC)
