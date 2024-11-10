-- //./Type.hs//

module HVML.Inject where

import Control.Monad (foldM)
import Data.Word
import HVML.Type
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as MS

type VarMap = IM.IntMap (Maybe Term)

injectCore :: Book -> Core -> Word64 -> VarMap -> HVM VarMap
injectCore _ Era loc vars = do
  set loc (termNew _ERA_ 0 0)
  return vars
injectCore book (Lam vr0 bod) loc vars = do
  lam   <- allocNode 2
  vars0 <- injectBind vr0 (termNew _VAR_ 0 (lam + 0)) vars
  vars1 <- injectCore book bod (lam + 1) vars0
  set loc (termNew _LAM_ 0 lam)
  return vars1
injectCore book (App fun arg) loc vars = do
  app   <- allocNode 2
  vars0 <- injectCore book fun (app + 0) vars
  vars1 <- injectCore book arg (app + 1) vars0
  set loc (termNew _APP_ 0 app)
  return vars1
injectCore book (Sup lab tm0 tm1) loc vars = do
  sup   <- allocNode 2
  vars0 <- injectCore book tm0 (sup + 0) vars
  vars1 <- injectCore book tm1 (sup + 1) vars0
  set loc (termNew _SUP_ lab sup)
  return vars1
injectCore book (Dup lab dp0 dp1 val bod) loc vars = do
  dup   <- allocNode 3
  vars0 <- injectBind dp0 (termNew _DP0_ lab dup) vars
  vars1 <- injectBind dp1 (termNew _DP1_ lab dup) vars0
  vars2 <- injectCore book val (dup + 2) vars1
  injectCore book bod loc vars2
injectCore book (Ref nam fid) loc vars = do
  set loc (termNew _REF_ 0 fid)
  return vars
injectCore book (Ctr cid fds) loc vars = do
  let arity = length fds
  ctr   <- allocNode (fromIntegral arity)
  vars0 <- foldM (\vs (ix,fd) -> injectCore book fd (ctr + ix) vs) vars (zip [0..] fds)
  set loc (termNew _CTR_ (u12v2New cid (fromIntegral (length fds))) ctr)
  return vars0
injectCore book (Mat val css) loc vars = do
  mat   <- allocNode (1 + fromIntegral (length css))
  vars0 <- injectCore book val (mat + 0) vars
  vars1 <- foldM (\vs (ix,bod) -> do
    injectCore book bod (mat + 1 + ix) vs) vars0 (zip [0..] css)
  set loc (termNew _MAT_ (fromIntegral (length css)) mat)
  return vars1
injectCore book (U32 val) loc vars = do
  set loc (termNew _W32_ 0 (fromIntegral val))
  return vars
injectCore book (Op2 opr nm0 nm1) loc vars = do
  opx   <- allocNode 2
  vars0 <- injectCore book nm0 (opx + 0) vars
  vars1 <- injectCore book nm1 (opx + 1) vars0
  set loc (termNew _OPX_ (fromIntegral $ fromEnum opr) opx)
  return vars1
injectCore _ (Var uid) loc vars = do
  let namHash = hash uid
  case IM.lookup namHash vars of
    Nothing -> return $ IM.insert namHash (Just loc) vars
    Just mOldVar -> case mOldVar of
      Nothing -> return $ IM.insert namHash (Just loc) vars
      Just oldVar -> do
        set loc oldVar
        return $ IM.insert namHash (Just loc) vars
  where
    hash :: String -> Int
    hash = foldl (\h c -> 33 * h + fromEnum c) 5381

injectBind :: String -> Term -> VarMap -> HVM VarMap
injectBind nam var vars = do
  let subKey = termKey var
  let namHash = hash nam
  case IM.lookup namHash vars of
    Nothing -> do
      set subKey (termNew _SUB_ 0 0)
      return $ IM.insert namHash (Just var) vars
    Just mOldVar -> case mOldVar of
      Nothing -> do
        set subKey (termNew _SUB_ 0 0)
        return $ IM.insert namHash (Just var) vars
      Just oldVar -> do
        set oldVar var
        set subKey (termNew _SUB_ 0 0)
        return $ IM.insert namHash (Just var) vars
  where
    hash :: String -> Int
    hash = foldl (\h c -> 33 * h + fromEnum c) 5381

doInjectCore :: Book -> Core -> HVM Term
doInjectCore book core = do
  injectCore book core 0 IM.empty
  got 0
