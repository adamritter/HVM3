module HVMS.Inject where

import Data.Word
import qualified Data.Map as Map
import HVMS.Type

-- Variable Map
type VarMap = Map.Map String Loc

-- Core to Runtime
-- --------------

injectPCore :: PCore -> Maybe Loc -> VarMap -> IO (VarMap, Term)
injectPCore (PVar name) loc vars = case (Map.lookup name vars, loc) of
  -- temporary node that will be mutated when the negative end of this variable is injected.
  (Nothing, Just pos_loc) -> return (Map.insert name pos_loc vars, termNew _NUL_ 0 0)
  (Just neg_loc, _      ) -> return (Map.delete name vars, termNew _VAR_ 0 neg_loc)
  _                       -> do
    putStrLn $ "injectPCore: invalid VAR (" ++ name ++ ")"
    return (vars, _VOID_)
injectPCore PNul _ vars =
  return (vars, termNew _NUL_ 0 0)
injectPCore (PLam var bod) loc vars = do
  lam <- allocNode 2
  (vars, var) <- injectNCore var (Just (lam + 0)) vars
  (vars, bod) <- injectPCore bod (Just (lam + 1)) vars
  set (lam + 0) var
  set (lam + 1) bod
  return (vars, termNew _LAM_ 0 lam)
injectPCore (PSup tm1 tm2) loc vars = do
  sup <- allocNode 2
  (vars, tm1) <- injectPCore tm1 (Just (sup + 0)) vars
  (vars, tm2) <- injectPCore tm2 (Just (sup + 1)) vars
  set (sup + 0) tm1
  set (sup + 1) tm2
  return (vars, termNew _SUP_ 0 sup)

injectNCore :: NCore -> Maybe Loc -> VarMap -> IO (VarMap, Term)
injectNCore (NSub name) loc vars = case (Map.lookup name vars, loc) of
  (Just pos_loc, Just neg_host) -> do
    -- we've seen the positive end of this var already, so we should mutate
    -- it to hold the SUB's location.
    set pos_loc (termNew _VAR_ 0 neg_host)
    return (Map.delete name vars, termNew _SUB_ 0 0)
  -- we haven't seen the positive end of this var yet, so we save the
  -- SUB's location so the VAR can reference it.
  (Nothing, Just neg_host)      -> return (Map.insert name neg_host vars, termNew _SUB_ 0 0)
  _                             -> do
    putStrLn $ "injectNCore: invalid SUB (" ++ name ++ ")"
    return (vars, _VOID_)
injectNCore NEra _ vars =
  return (vars, termNew _ERA_ 0 0)
injectNCore (NApp arg ret) loc vars = do
  app <- allocNode 2
  (vars, arg) <- injectPCore arg (Just (app + 0)) vars
  (vars, ret) <- injectNCore ret (Just (app + 1)) vars
  set (app + 0) arg
  set (app + 1) ret
  return (vars, termNew _APP_ 0 app)
injectNCore (NDup dp1 dp2) loc vars = do
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
  rbagPush neg pos
  return vars

injectNet :: Net -> VarMap -> IO (VarMap, Term)
injectNet (Net root bag) vars = do
  root_loc <- allocNode 1
  (vars, root) <- injectPCore root (Just root_loc) vars
  vars <- foldr (\dex acc -> acc >>= injectDex dex) (return vars) bag
  root <- get root_loc
  return (vars, root)

-- Main Entry Points
-- ----------------

doInjectNet :: Net -> IO Term
doInjectNet net = do
  (_, root) <- injectNet net Map.empty
  return root
