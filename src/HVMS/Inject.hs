module HVMS.Inject where

import Data.Word
import qualified Data.Map as Map
import HVMS.Type

-- Variable Map
type VarMap = Map.Map String Word64

-- Core to Runtime
-- --------------

injectPCore :: PCore -> Maybe Word64 -> VarMap -> IO (VarMap, Term)
injectPCore (PVar nam) host vars = case Map.lookup nam vars of
  Just neg_host -> return (vars, termNew _VAR_ 0 neg_host)
  Nothing       -> return (vars, termNew _NUL_ 0 0)
injectPCore PNul _ vars =
  return (vars, termNew _NUL_ 0 0)
injectPCore (PLam var bod) host vars = do
  lam <- allocNode 2
  (vars, var) <- injectNCore var (Just (lam + 0)) vars
  (vars, bod) <- injectPCore bod (Just (lam + 1)) vars
  set (lam + 0) var
  set (lam + 1) bod
  return (vars, termNew _LAM_ 0 lam)
injectPCore (PSup tm1 tm2) host vars = do
  sup <- allocNode 2
  (vars, tm1) <- injectPCore tm1 (Just (sup + 0)) vars
  (vars, tm2) <- injectPCore tm2 (Just (sup + 1)) vars
  set (sup + 0) tm1
  set (sup + 1) tm2
  return (vars, termNew _SUP_ 0 sup)

injectNCore :: NCore -> Maybe Word64 -> VarMap -> IO (VarMap, Term)
injectNCore (NSub nam) host vars = case Map.lookup nam vars of
  Just pos_host -> return (vars, termNew _SUB_ 0 pos_host)
  Nothing       -> return (vars, termNew _ERA_ 0 0)
injectNCore NEra _ vars =
  return (vars, termNew _ERA_ 0 0)
injectNCore (NApp arg ret) host vars = do
  app <- allocNode 2
  (vars, arg) <- injectPCore arg (Just (app + 0)) vars
  (vars, ret) <- injectNCore ret (Just (app + 1)) vars
  set (app + 0) arg
  set (app + 1) ret
  return (vars, termNew _APP_ 0 app)
injectNCore (NDup dp1 dp2) host vars = do
  dup <- allocNode 2
  (vars, dp1) <- injectNCore dp1 (Just (dup + 0)) vars
  (vars, dp2) <- injectNCore dp2 (Just (dup + 1)) vars
  set (dup + 0) dp1
  set (dup + 1) dp2
  return (vars, termNew _DUP_ 0 dup)

-- Dex and Net Injection
-- --------------------

injectDex :: Dex -> VarMap -> IO VarMap
injectDex (neg, pos) vars = do
  (vars, neg) <- injectNCore neg Nothing vars
  (vars, pos) <- injectPCore pos Nothing vars
  loc <- allocNode 2
  set (loc + 0) neg
  set (loc + 1) pos
  return vars

injectNet :: Net -> VarMap -> IO (VarMap, Term)
injectNet (Net rot bag) vars = do
  (vars, rot) <- injectPCore rot (Just 0) vars
  vars <- foldr (\dex acc -> acc >>= injectDex dex) (return vars) bag
  return (vars, rot)

-- Main Entry Points
-- ----------------

doInjectNet :: Net -> IO Term
doInjectNet net = do
  (_, root) <- injectNet net Map.empty
  return root
