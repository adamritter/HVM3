-- //./Type.hs//

module HVML.Inject where

-- import Control.Monad (foldM)
-- import Control.Monad.State
-- import Data.Word
-- import HVML.Type
-- import qualified Data.IntMap.Strict as IM

-- type InjectM a = StateT (IM.IntMap (Maybe Term)) HVM a

-- injectCore :: Book -> Core -> Loc -> InjectM ()
-- injectCore _ Era loc = do
  -- lift $ set loc (termNew _ERA_ 0 0)

-- injectCore book (Lam vr0 bod) loc = do
  -- lam <- lift $ allocNode 2
  -- injectBind vr0 (termNew _VAR_ 0 (lam + 0))
  -- injectCore book bod (lam + 1)
  -- lift $ set loc (termNew _LAM_ 0 lam)

-- injectCore book (App fun arg) loc = do
  -- app <- lift $ allocNode 2
  -- injectCore book fun (app + 0)
  -- injectCore book arg (app + 1)
  -- lift $ set loc (termNew _APP_ 0 app)

-- injectCore book (Sup lab tm0 tm1) loc = do
  -- sup <- lift $ allocNode 2
  -- injectCore book tm0 (sup + 0)
  -- injectCore book tm1 (sup + 1)
  -- lift $ set loc (termNew _SUP_ lab sup)

-- injectCore book (Dup lab dp0 dp1 val bod) loc = do
  -- dup <- lift $ allocNode 3
  -- injectBind dp0 (termNew _DP0_ lab dup)
  -- injectBind dp1 (termNew _DP1_ lab dup)
  -- injectCore book val (dup + 2)
  -- injectCore book bod loc

-- injectCore book (Ref nam fid) loc = do
  -- lift $ set loc (termNew _REF_ 0 fid)

-- injectCore book (Ctr cid fds) loc = do
  -- let arity = length fds
  -- ctr <- lift $ allocNode (fromIntegral arity)
  -- sequence_ [injectCore book fd (ctr + ix) | (ix,fd) <- zip [0..] fds]
  -- lift $ set loc (termNew _CTR_ (u12v2New cid (fromIntegral arity)) ctr)

-- injectCore book (Mat val css) loc = do
  -- mat <- lift $ allocNode (1 + fromIntegral (length css))
  -- injectCore book val (mat + 0)
  -- sequence_ [injectCore book bod (mat + 1 + ix) | (ix,bod) <- zip [0..] css]
  -- lift $ set loc (termNew _MAT_ (fromIntegral (length css)) mat)

-- injectCore book (U32 val) loc = do
  -- lift $ set loc (termNew _W32_ 0 (fromIntegral val))

-- injectCore book (Op2 opr nm0 nm1) loc = do
  -- opx <- lift $ allocNode 2
  -- injectCore book nm0 (opx + 0)
  -- injectCore book nm1 (opx + 1)
  -- lift $ set loc (termNew _OPX_ (fromIntegral $ fromEnum opr) opx)

-- injectCore _ (Var uid) loc = do
  -- let namHash = hash uid
  -- vars <- get
  -- case IM.lookup namHash vars of
    -- Nothing -> put $ IM.insert namHash (Just loc) vars
    -- Just mOldVar -> case mOldVar of
      -- Nothing -> put $ IM.insert namHash (Just loc) vars
      -- Just oldVar -> do
        -- lift $ set loc oldVar
        -- put $ IM.insert namHash (Just loc) vars
  -- where
    -- hash = foldl (\h c -> 33 * h + fromEnum c) 5381

-- injectBind :: String -> Term -> InjectM ()
-- injectBind nam var = do
  -- let subKey = termKey var
  -- let namHash = hash nam
  -- vars <- get
  -- case IM.lookup namHash vars of
    -- Nothing -> do
      -- lift $ set subKey (termNew _SUB_ 0 0)
      -- put $ IM.insert namHash (Just var) vars
    -- Just mOldVar -> case mOldVar of
      -- Nothing -> do
        -- lift $ set subKey (termNew _SUB_ 0 0)
        -- put $ IM.insert namHash (Just var) vars
      -- Just oldVar -> do
        -- lift $ set oldVar var
        -- lift $ set subKey (termNew _SUB_ 0 0)
        -- put $ IM.insert namHash (Just var) vars
  -- where
    -- hash = foldl (\h c -> 33 * h + fromEnum c) 5381

-- doInjectCore :: Book -> Core -> HVM Term
-- doInjectCore book core = do
  -- evalStateT (injectCore book core 0) IM.empty
  -- got 0

-- TODO: refactor this to use a similar algorithm to Compile.hs
-- for handling variables. that is, we should keep a map of args,
-- and a list of vars found. and we should only set the variables
-- AFTER injectCore has fully returned.
-- remember: we should keep two states:
-- args : var_name => binder_host
-- vars : [(var_name, var_host)]
-- do you understand the assignment? answer below in english

-- Yes, I understand the assignment. The goal is to refactor the variable handling in injectCore to:

-- 1. Use two separate state components:
   -- - args: A map from variable names to their binder locations (where variables are bound)
   -- - vars: A list of tuples containing variable names and their usage locations

-- 2. Change the algorithm to:
   -- - First traverse the term collecting all variable usages without setting them
   -- - Only after the full traversal is complete, go through the vars list and set the appropriate references

-- This approach would be more similar to Compile.hs and would handle variable scoping more cleanly by separating the collection of variable information from the actual setting of references in memory.

-- The key difference from the current implementation is that variable references would not be set immediately during traversal, but rather collected and processed in a second pass after the full term structure is built.

-- yes. remember: we always set the LAM binder (lam + 0) to SUB, and the DUP binders (dup + 0 and dup + 1) to SUB too. then, we register var, or dp0/dp1, to point to the respective binder locations (with a VAR/DP0/DP1 term). on variables, we just return a '0' as a placeholder. then, after all is done, we set all vars, similar to the 'makeVarLine' logic on the compiler.


import Control.Monad (foldM)
import Control.Monad.State
import Data.Word
import HVML.Type
import qualified Data.Map.Strict as Map

type InjectM a = StateT InjectState HVM a

data InjectState = InjectState
  { args :: Map.Map String Term  -- maps var names to binder locations
  , vars :: [(String, Loc)]     -- list of (var name, usage location) pairs
  }

emptyState :: InjectState
emptyState = InjectState Map.empty []

injectCore :: Book -> Core -> Loc -> InjectM ()
injectCore _ Era loc = do
  lift $ set loc (termNew _ERA_ 0 0)

injectCore book (Lam vr0 bod) loc = do
  lam <- lift $ allocNode 2
  lift $ set (lam + 0) (termNew _SUB_ 0 0)
  modify $ \s -> s { args = Map.insert vr0 (termNew _VAR_ 0 (lam + 0)) (args s) }
  injectCore book bod (lam + 1)
  lift $ set loc (termNew _LAM_ 0 lam)

injectCore book (App fun arg) loc = do
  app <- lift $ allocNode 2
  injectCore book fun (app + 0)
  injectCore book arg (app + 1)
  lift $ set loc (termNew _APP_ 0 app)

injectCore book (Sup lab tm0 tm1) loc = do
  sup <- lift $ allocNode 2
  injectCore book tm0 (sup + 0)
  injectCore book tm1 (sup + 1)
  lift $ set loc (termNew _SUP_ lab sup)

injectCore book (Dup lab dp0 dp1 val bod) loc = do
  dup <- lift $ allocNode 3
  lift $ set (dup + 0) (termNew _SUB_ 0 0)
  lift $ set (dup + 1) (termNew _SUB_ 0 0)
  modify $ \s -> s 
    { args = Map.insert dp0 (termNew _DP0_ lab dup) 
           $ Map.insert dp1 (termNew _DP1_ lab dup) (args s) 
    }
  injectCore book val (dup + 2)
  injectCore book bod loc

injectCore book (Ref nam fid) loc = do
  lift $ set loc (termNew _REF_ 0 fid)

injectCore book (Ctr cid fds) loc = do
  let arity = length fds
  ctr <- lift $ allocNode (fromIntegral arity)
  sequence_ [injectCore book fd (ctr + ix) | (ix,fd) <- zip [0..] fds]
  lift $ set loc (termNew _CTR_ (u12v2New cid (fromIntegral arity)) ctr)

injectCore book (Mat val css) loc = do
  mat <- lift $ allocNode (1 + fromIntegral (length css))
  injectCore book val (mat + 0)
  sequence_ [injectCore book bod (mat + 1 + ix) | (ix,bod) <- zip [0..] css]
  lift $ set loc (termNew _MAT_ (fromIntegral (length css)) mat)

injectCore book (U32 val) loc = do
  lift $ set loc (termNew _W32_ 0 (fromIntegral val))

injectCore book (Op2 opr nm0 nm1) loc = do
  opx <- lift $ allocNode 2
  injectCore book nm0 (opx + 0)
  injectCore book nm1 (opx + 1)
  lift $ set loc (termNew _OPX_ (fromIntegral $ fromEnum opr) opx)

injectCore _ (Var nam) loc = do
  modify $ \s -> s { vars = (nam, loc) : vars s }
  lift $ set loc 0 -- placeholder

doInjectCore :: Book -> Core -> HVM Term
doInjectCore book core = do
  (_, state) <- runStateT (injectCore book core 0) emptyState
  -- Set all variables after the structure is built
  mapM_ (setVar (args state)) (vars state)
  got 0
  where
    setVar args (name, loc) = case Map.lookup name args of
      Just term -> set loc term
      Nothing   -> error $ "Unbound variable: " ++ name


