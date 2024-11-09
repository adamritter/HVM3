-- //./Type.hs//

module HVML.Compile where

import Control.Monad.State
import Data.Word
import HVML.Show
import HVML.Type
import qualified Data.Map.Strict as MS

-- Compilation
-- -----------

data CompileState = CompileState
  { next :: Word64
  , args :: MS.Map String String  -- var_name => binder_host
  , vars :: [(String, String)]     -- [(var_name, var_host)]
  , code :: [String]
  }

type Compile = State CompileState

compile :: Book -> Word64 -> Core -> String
compile book fid core = unlines
  [ "Term F_" ++ show fid ++ "() {"
  -- , "  printf(\"calling " ++ name ++ "\\n\");"
  , unlines (reverse (varLines ++ code st))
  , "  return " ++ result ++ ";"
  , "}"
  ]
  where
    (result, st) = runState (compileCore book core "root") $ CompileState 0 MS.empty [] []
    varLines     = map makeVarLine (vars st)
    makeVarLine  = \ (var, host) ->
      "  set(" ++ host ++ ", " ++ (MS.findWithDefault "?" var (args st)) ++ ");"

emit :: String -> Compile ()
emit line = modify $ \s -> s { code = line : code s }

fresh :: Compile Word64
fresh = do
  uid <- gets next
  modify $ \s -> s { next = uid + 1 }
  return uid

bind :: String -> String -> Compile ()
bind var host = modify $ \s -> s { args = MS.insert var host (args s) }

addVar :: String -> String -> Compile ()
addVar var host = modify $ \s -> s { vars = (var, host) : vars s }

compileCore :: Book -> Core -> String -> Compile String
compileCore _ Era _ = 
  return $ "term_new(ERA, 0, 0)"
compileCore _ (Var name) host = do
  addVar name host
  return $ "0" -- placeholder, will be set later
compileCore book (Lam var bod) host = do
  uid <- fresh
  let lamName = "lam" ++ show uid
  emit $ "  Loc " ++ lamName ++ " = alloc_node(2);"
  emit $ "  set(" ++ lamName ++ " + 0, term_new(SUB, 0, 0));"
  bind var $ "term_new(VAR, 0, " ++ lamName ++ " + 0)"
  bodT <- compileCore book bod (lamName ++ " + 1")
  emit $ "  set(" ++ lamName ++ " + 1, " ++ bodT ++ ");"
  return $ "term_new(LAM, 0, " ++ lamName ++ ")"
compileCore book (App fun arg) host = do
  uid <- fresh
  let appName = "app" ++ show uid
  emit $ "  Loc " ++ appName ++ " = alloc_node(2);"
  funT <- compileCore book fun (appName ++ " + 0")
  argT <- compileCore book arg (appName ++ " + 1")
  emit $ "  set(" ++ appName ++ " + 0, " ++ funT ++ ");"
  emit $ "  set(" ++ appName ++ " + 1, " ++ argT ++ ");"
  return $ "term_new(APP, 0, " ++ appName ++ ")"
compileCore book (Sup tm0 tm1) host = do
  uid <- fresh
  let supName = "sup" ++ show uid
  emit $ "  Loc " ++ supName ++ " = alloc_node(2);"
  tm0T <- compileCore book tm0 (supName ++ " + 0")
  tm1T <- compileCore book tm1 (supName ++ " + 1")
  emit $ "  set(" ++ supName ++ " + 0, " ++ tm0T ++ ");"
  emit $ "  set(" ++ supName ++ " + 1, " ++ tm1T ++ ");"
  return $ "term_new(SUP, 0, " ++ supName ++ ")"
compileCore book (Dup dp0 dp1 val bod) host = do
  uid <- fresh
  let dupName = "dup" ++ show uid
  emit $ "  Loc " ++ dupName ++ " = alloc_node(3);"
  emit $ "  set(" ++ dupName ++ " + 0, term_new(SUB, 0, 0));"
  emit $ "  set(" ++ dupName ++ " + 1, term_new(SUB, 0, 0));"
  bind dp0 $ "term_new(DP0, 0, " ++ dupName ++ " + 0)"
  bind dp1 $ "term_new(DP1, 0, " ++ dupName ++ " + 0)"
  valT <- compileCore book val (dupName ++ " + 2")
  emit $ "  set(" ++ dupName ++ " + 2, " ++ valT ++ ");"
  bodT <- compileCore book bod host
  return bodT
compileCore book (Ref nam fid) _ =
  return $ "term_new(REF, 0, " ++ show fid ++ ")"
