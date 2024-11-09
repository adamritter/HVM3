-- //./Type.hs//

module HVML.Inject where

import Data.Word
import HVML.Type
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as MS

type VarMap = IM.IntMap (Maybe Term)

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

injectCore :: Fids -> Core -> Word64 -> VarMap -> HVM VarMap
injectCore _ Era loc vars = do
  set loc (termNew _ERA_ 0 0)
  return vars
injectCore fids (Lam vr0 bod) loc vars = do
  lam   <- allocNode 2
  vars0 <- injectBind vr0 (termNew _VAR_ 0 (lam + 0)) vars
  vars1 <- injectCore fids bod (lam + 1) vars0
  set loc (termNew _LAM_ 0 lam)
  return vars1
injectCore fids (App fun arg) loc vars = do
  app   <- allocNode 2
  vars0 <- injectCore fids fun (app + 0) vars
  vars1 <- injectCore fids arg (app + 1) vars0
  set loc (termNew _APP_ 0 app)
  return vars1
injectCore fids (Sup tm0 tm1) loc vars = do
  sup   <- allocNode 2
  vars0 <- injectCore fids tm0 (sup + 0) vars
  vars1 <- injectCore fids tm1 (sup + 1) vars0
  set loc (termNew _SUP_ 0 sup)
  return vars1
injectCore fids (Dup dp0 dp1 val bod) loc vars = do
  dup   <- allocNode 3
  vars0 <- injectBind dp0 (termNew _DP0_ 0 dup) vars
  vars1 <- injectBind dp1 (termNew _DP1_ 0 dup) vars0
  vars2 <- injectCore fids val (dup + 2) vars1
  injectCore fids bod loc vars2
injectCore fids (Ref nam) loc vars = do
  case MS.lookup nam fids of
    Just fid -> set loc (termNew _REF_ 0 fid)
    Nothing  -> error $ "Undefined reference: " ++ nam
  return vars
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

doInjectCore :: Fids -> Core -> HVM Term
doInjectCore fids core = do
  injectCore fids core 0 IM.empty
  got 0
