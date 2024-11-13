-- //./Type.hs//

module HVML.Compile where

import Control.Monad (forM_, forM)
import Control.Monad.State
import Data.List
import Data.Word
import HVML.Show
import HVML.Type
import qualified Data.Map.Strict as MS

import Debug.Trace

-- Compilation
-- -----------

data CompileState = CompileState
  { next :: Word64
  , tabs :: Int
  , bins :: MS.Map String String  -- var_name => binder_host
  , vars :: [(String, String)]    -- [(var_name, var_host)]
  , code :: [String]
  }

type Compile = State CompileState

compile :: Book -> Word64 -> String
compile book fid =
  let full = compileWith compileFull book fid in
  let fast = compileWith compileFast book fid in
  let slow = compileWith compileSlow book fid in
  if "<ERR>" `isInfixOf` fast
    then unlines [ full , slow ]
    else unlines [ full , fast ]

-- Compiles a function using either Fast-Mode or Full-Mode
compileWith :: (Book -> Word64 -> Core -> [String] -> Compile ()) -> Book -> Word64 -> String
compileWith cmp book fid = 
  let args   = fst (idToFunc book MS.! fid) in
  let core   = snd (idToFunc book MS.! fid) in
  let state  = CompileState 0 0 MS.empty [] [] in
  let result = runState (cmp book fid core args) state in
  unlines $ reverse $ code (snd result)

emit :: String -> Compile ()
emit line = modify $ \st -> st { code = (replicate (tabs st * 2) ' ' ++ line) : code st }

tabInc :: Compile ()
tabInc = modify $ \st -> st { tabs = tabs st + 1 }

tabDec :: Compile ()
tabDec = modify $ \st -> st { tabs = tabs st - 1 }

bind :: String -> String -> Compile ()
bind var host = modify $ \st -> st { bins = MS.insert var host (bins st) }

fresh :: Compile Word64
fresh = do
  uid <- gets next
  modify $ \s -> s { next = uid + 1 }
  return uid

-- Full Compiler
-- -------------

compileFull :: Book -> Word64 -> Core -> [String] -> Compile ()
compileFull book fid core args = do
  emit $ "Term " ++ idToName book MS.! fid ++ "_t(Term ref) {"
  tabInc
  forM_ (zip [0..] args) $ \(i, arg) -> do
    bind arg $ "got(term_loc(ref) + " ++ show i ++ ")"
  result <- compileFullCore book fid core "root"
  st <- get
  forM_ (vars st) $ \ (var,host) -> do
    let varTerm = MS.findWithDefault "" var (bins st)
    emit $ "set(" ++ host ++ ", " ++ varTerm ++ ");"
  emit $ "return " ++ result ++ ";"
  tabDec
  emit "}"

compileFullVar :: String -> String -> Compile String
compileFullVar var host = do
  bins <- gets bins
  case MS.lookup var bins of
    Just entry -> do
      return entry
    Nothing -> do
      modify $ \s -> s { vars = (var, host) : vars s }
      return "0"

compileFullCore :: Book -> Word64 -> Core -> String -> Compile String
compileFullCore book fid Era _ = 
  return $ "term_new(ERA, 0, 0)"
compileFullCore book fid (Var name) host = do
  compileFullVar name host
compileFullCore book fid (Lam var bod) host = do
  uid <- fresh
  let lamName = "lam" ++ show uid
  emit $ "Loc " ++ lamName ++ " = alloc_node(2);"
  emit $ "set(" ++ lamName ++ " + 0, term_new(SUB, 0, 0));"
  bind var $ "term_new(VAR, 0, " ++ lamName ++ " + 0)"
  bodT <- compileFullCore book fid bod (lamName ++ " + 1")
  emit $ "set(" ++ lamName ++ " + 1, " ++ bodT ++ ");"
  return $ "term_new(LAM, 0, " ++ lamName ++ ")"
compileFullCore book fid (App fun arg) host = do
  uid <- fresh
  let appName = "app" ++ show uid
  emit $ "Loc " ++ appName ++ " = alloc_node(2);"
  funT <- compileFullCore book fid fun (appName ++ " + 0")
  argT <- compileFullCore book fid arg (appName ++ " + 1")
  emit $ "set(" ++ appName ++ " + 0, " ++ funT ++ ");"
  emit $ "set(" ++ appName ++ " + 1, " ++ argT ++ ");"
  return $ "term_new(APP, 0, " ++ appName ++ ")"
compileFullCore book fid (Sup lab tm0 tm1) host = do
  uid <- fresh
  let supName = "sup" ++ show uid
  emit $ "Loc " ++ supName ++ " = alloc_node(2);"
  tm0T <- compileFullCore book fid tm0 (supName ++ " + 0")
  tm1T <- compileFullCore book fid tm1 (supName ++ " + 1")
  emit $ "set(" ++ supName ++ " + 0, " ++ tm0T ++ ");"
  emit $ "set(" ++ supName ++ " + 1, " ++ tm1T ++ ");"
  return $ "term_new(SUP, " ++ show lab ++ ", " ++ supName ++ ")"
compileFullCore book fid (Dup lab dp0 dp1 val bod) host = do
  uid <- fresh
  let dupName = "dup" ++ show uid
  emit $ "Loc " ++ dupName ++ " = alloc_node(3);"
  emit $ "set(" ++ dupName ++ " + 0, term_new(SUB, 0, 0));"
  emit $ "set(" ++ dupName ++ " + 1, term_new(SUB, 0, 0));"
  bind dp0 $ "term_new(DP0, " ++ show lab ++ ", " ++ dupName ++ " + 0)"
  bind dp1 $ "term_new(DP1, " ++ show lab ++ ", " ++ dupName ++ " + 0)"
  valT <- compileFullCore book fid val (dupName ++ " + 2")
  emit $ "set(" ++ dupName ++ " + 2, " ++ valT ++ ");"
  bodT <- compileFullCore book fid bod host
  return bodT
compileFullCore book fid (Ctr cid fds) host = do
  uid <- fresh
  let ctrName = "ctr" ++ show uid
  let arity = length fds
  emit $ "Loc " ++ ctrName ++ " = alloc_node(" ++ show arity ++ ");"
  fdsT <- mapM (\ (i,fd) -> compileFullCore book fid fd (ctrName ++ " + " ++ show i)) (zip [0..] fds)
  sequence_ [emit $ "set(" ++ ctrName ++ " + " ++ show i ++ ", " ++ fdT ++ ");" | (i,fdT) <- zip [0..] fdsT]
  return $ "term_new(CTR, u12v2_new(" ++ show cid ++ ", " ++ show arity ++ "), " ++ ctrName ++ ")"
compileFullCore book fid (Mat val css) host = do
  uid <- fresh
  let matName = "mat" ++ show uid
  let arity = length css
  emit $ "Loc " ++ matName ++ " = alloc_node(" ++ show (1 + arity) ++ ");"
  valT <- compileFullCore book fid val (matName ++ " + 0")
  emit $ "set(" ++ matName ++ " + 0, " ++ valT ++ ");"
  cssT <- mapM (\ (i,(_,cs)) -> compileFullCore book fid cs (matName ++ " + " ++ show (i+1))) (zip [0..] css)
  sequence_ [emit $ "set(" ++ matName ++ " + " ++ show (i+1) ++ ", " ++ csT ++ ");" | (i,csT) <- zip [0..] cssT]
  return $ "term_new(MAT, " ++ show arity ++ ", " ++ matName ++ ")"
compileFullCore book fid (U32 val) _ =
  return $ "term_new(W32, 0, " ++ show (fromIntegral val) ++ ")"
compileFullCore book fid (Op2 opr nu0 nu1) host = do
  opxUid <- fresh
  opxNam <- return $ "opx" ++ show opxUid
  emit $ "Loc " ++ opxNam ++ " = alloc_node(2);"
  nu0T <- compileFullCore book fid nu0 (opxNam ++ " + 0")
  nu1T <- compileFullCore book fid nu1 (opxNam ++ " + 1")
  emit $ "set(" ++ opxNam ++ " + 0, " ++ nu0T ++ ");"
  emit $ "set(" ++ opxNam ++ " + 1, " ++ nu1T ++ ");"
  return $ "term_new(OPX, " ++ show (fromEnum opr) ++ ", " ++ opxNam ++ ")"
compileFullCore book fid (Ref rNam rFid rArg) host = do
  uid <- fresh
  let refName = "ref" ++ show uid
  let arity = length rArg
  emit $ "Loc " ++ refName ++ " = alloc_node(" ++ show arity ++ ");"
  argsT <- mapM (\ (i,arg) -> compileFullCore book fid arg (refName ++ " + " ++ show i)) (zip [0..] rArg)
  sequence_ [emit $ "set(" ++ refName ++ " + " ++ show i ++ ", " ++ argT ++ ");" | (i,argT) <- zip [0..] argsT]
  return $ "term_new(REF, u12v2_new(" ++ show rFid ++ ", " ++ show arity ++ "), " ++ refName ++ ")"

-- Fast Compiler
-- -------------

-- Compiles a function using Fast-Mode
compileFast :: Book -> Word64 -> Core -> [String] -> Compile ()
compileFast book fid core args = do
  emit $ "Term " ++ idToName book MS.! fid ++ "_f(Term ref) {"
  tabInc
  emit "u64 itrs = 0;"
  args <- forM (zip [0..] args) $ \ (i, arg) -> do
    argUid <- fresh
    argNam <- return $ "arg" ++ show argUid
    emit $ "Term " ++ argNam ++ " = got(term_loc(ref) + " ++ show i ++ ");"
    bind arg argNam
    return argNam
  compileFastArgs book fid core args
  tabDec
  emit "}"

-- Compiles a fast function's argument list
compileFastArgs :: Book -> Word64 -> Core -> [String] -> Compile ()
compileFastArgs book fid body ctx = do
  emit $ "while (1) {"
  tabInc
  compileFastBody book fid body ctx 0
  tabDec
  emit $ "}"

-- Compiles a fast function body (pattern-matching)
compileFastBody :: Book -> Word64 -> Core -> [String] -> Int -> Compile ()
compileFastBody book fid term@(Mat val css) ctx itr = do
  valT   <- compileFastCore book fid val
  valUid <- fresh
  valNam <- return $ "val" ++ show valUid
  numUid <- fresh
  numNam <- return $ "num" ++ show numUid
  emit $ "Term " ++ valNam ++ " = reduce(" ++ valT ++ ");"
  let isNumeric = length css > 0 && fst (css !! 0) == -1
  -- Numeric Pattern-Matching
  if isNumeric then do
    emit $ "if (term_tag(" ++ valNam ++ ") == W32) {"
    tabInc
    emit $ "u32 " ++ numNam ++ " = term_loc(" ++ valNam ++ ");"
    emit $ "switch (" ++ numNam ++ ") {"
    tabInc
    forM_ (zip [0..] css) $ \ (i, (_,cs)) -> do
      if i < length css - 1 then do
        emit $ "case " ++ show i ++ ": {"
        tabInc
        compileFastBody book fid cs ctx (itr + 1)
        emit $ "break;"
        tabDec
        emit $ "}"
      else do
        emit $ "default: {"
        tabInc
        preUid <- fresh
        preNam <- return $ "pre" ++ show preUid
        emit $ "Term " ++ preNam ++ " = " ++ "term_new(W32, 0, "++numNam++" - "++show (length css - 1)++");"
        compileFastApps book fid cs [preNam] ctx (itr + 1 + 1)
        emit $ "break;"
        tabDec
        emit $ "}"
    tabDec
    emit $ "}"
    tabDec
    emit $ "}"
  -- Constructor Pattern-Matching
  else do
    emit $ "if (term_tag(" ++ valNam ++ ") == CTR) {"
    tabInc
    emit $ "switch (u12v2_x(term_lab(" ++ valNam ++ "))) {"
    tabInc
    forM_ (zip [0..] css) $ \ (i, (ar,cs)) -> do
      emit $ "case " ++ show i ++ ": {"
      tabInc
      args <- if ar == 0
        then return []
        else forM [0..ar-1] $ \k -> do
          ctrUid <- fresh
          ctrNam <- return $ "ctr" ++ show ctrUid
          emit $ "Term " ++ ctrNam ++ " = got(term_loc(" ++ valNam ++ ") + " ++ show k ++ ");"
          return ctrNam
      compileFastApps book fid cs args ctx (itr + 1 + fromIntegral ar)
      emit $ "break;"
      tabDec
      emit $ "}"
    tabDec
    emit $ "}"
    tabDec
    emit $ "}"
  compileFastUndo book fid term ctx itr
compileFastBody book fid term@(Ref fNam fFid fArg) ctx itr | fFid == fid = do
  forM_ (zip fArg ctx) $ \ (arg, ctxVar) -> do
    argT <- compileFastCore book fid arg
    emit $ "" ++ ctxVar ++ " = " ++ argT ++ ";"
  emit $ "itrs += " ++ show (itr + 1) ++ ";"
  emit $ "continue;"
compileFastBody book fid term ctx itr = do
  emit $ "itrs += " ++ show (itr) ++ ";"
  body <- compileFastCore book fid term
  compileFastSave book fid term ctx itr
  emit $ "return " ++ body ++ ";"

-- compileFastBody book fid term ctx itr = do
  -- let (callFid, callArgs) = getCall term
  -- -- trace (coreToString term ++ " ||| " ++ show (length callArgs) ++ " " ++ show (length ctx) ++ " " ++ show callFid ++ " " ++ show fid) $ do
  -- if length callArgs == length ctx && callFid == fid then do
    -- forM_ (zip callArgs ctx) $ \ (arg, ctxVar) -> do
      -- argT <- compileFastCore book fid arg
      -- emit $ "" ++ ctxVar ++ " = " ++ argT ++ ";"
    -- emit $ "itrs += " ++ show (length ctx + itr + 1) ++ ";"
    -- emit $ "continue;"
  -- else do
    -- emit $ "itrs += " ++ show (length ctx + itr) ++ ";"
    -- body <- compileFastCore book fid term
    -- compileFastSave book fid term ctx itr
    -- emit $ "return " ++ body ++ ";"
  -- where
    -- getCall :: Core -> (Word64, [Core])
    -- getCall = go [] where
      -- go ctx (App f x) = go (x:ctx) f
      -- go ctx (Ref _ i) = (i, ctx)
      -- go ctx term      = (0xFFFFFFFF, ctx)

-- ...
compileFastApps :: Book -> Word64 -> Core -> [String] -> [String] -> Int -> Compile ()
compileFastApps book fid (Lam pvar pbod) (arg : args) ctx itr = do
  bind pvar $ arg
  compileFastApps book fid pbod args ctx itr
compileFastApps book fid term [] ctx itr =
  compileFastBody book fid term ctx itr
compileFastApps book fid term args ctx itr =
  error "TODO"

-- Falls back from fast mode to full mode
compileFastUndo :: Book -> Word64 -> Core -> [String] -> Int -> Compile ()
compileFastUndo book fid term ctx itr = do
  forM_ (zip [0..] ctx) $ \ (i, arg) -> do
    emit $ "set(term_loc(ref) + "++show i++", " ++ arg ++ ");"
  emit $ "return " ++ idToName book MS.! fid ++ "_t(ref);"

-- Completes a fast mode call
compileFastSave :: Book -> Word64 -> Core -> [String] -> Int -> Compile ()
compileFastSave book fid term ctx itr = do
  emit $ "*HVM.itrs += itrs;"

-- Compiles a core term in fast more
compileFastCore :: Book -> Word64 -> Core -> Compile String
compileFastCore book fid Era = 
  return $ "term_new(ERA, 0, 0)"
compileFastCore book fid (Var name) = do
  compileFastVar name
compileFastCore book fid (Lam var bod) = do
  uid <- fresh
  let lamName = "lam" ++ show uid
  emit $ "Loc " ++ lamName ++ " = alloc_node(2);"
  emit $ "set(" ++ lamName ++ " + 0, term_new(SUB, 0, 0));"
  bind var $ "term_new(VAR, 0, " ++ lamName ++ " + 0)"
  bodT <- compileFastCore book fid bod
  emit $ "set(" ++ lamName ++ " + 1, " ++ bodT ++ ");"
  return $ "term_new(LAM, 0, " ++ lamName ++ ")"
compileFastCore book fid (App fun arg) = do
  uid <- fresh
  let appName = "app" ++ show uid
  emit $ "Loc " ++ appName ++ " = alloc_node(2);"
  funT <- compileFastCore book fid fun
  argT <- compileFastCore book fid arg
  emit $ "set(" ++ appName ++ " + 0, " ++ funT ++ ");"
  emit $ "set(" ++ appName ++ " + 1, " ++ argT ++ ");"
  return $ "term_new(APP, 0, " ++ appName ++ ")"
compileFastCore book fid (Sup lab tm0 tm1) = do
  uid <- fresh
  let supName = "sup" ++ show uid
  emit $ "Loc " ++ supName ++ " = alloc_node(2);"
  tm0T <- compileFastCore book fid tm0
  tm1T <- compileFastCore book fid tm1
  emit $ "set(" ++ supName ++ " + 0, " ++ tm0T ++ ");"
  emit $ "set(" ++ supName ++ " + 1, " ++ tm1T ++ ");"
  return $ "term_new(SUP, " ++ show lab ++ ", " ++ supName ++ ")"
compileFastCore book fid (Dup lab dp0 dp1 val bod) = do
  dupUid <- fresh
  dupNam <- return $ "dup" ++ show dupUid
  dp0Uid <- fresh
  dp0Nam <- return $ "dp0" ++ show dp0Uid
  dp1Uid <- fresh
  dp1Nam <- return $ "dp1" ++ show dp1Uid
  valUid <- fresh
  valNam <- return $ "val" ++ show valUid
  valT   <- compileFastCore book fid val
  emit $ "Term " ++ valNam ++ " = reduce(" ++ valT ++ ");"
  emit $ "Term " ++ dp0Nam ++ ";"
  emit $ "Term " ++ dp1Nam ++ ";"
  emit $ "if (term_tag(" ++ valNam ++ ") == W32) {"
  tabInc
  emit $ "itrs += 1;"
  emit $ dp0Nam ++ " = " ++ valNam ++ ";"
  emit $ dp1Nam ++ " = " ++ valNam ++ ";"
  tabDec
  emit $ "} else {"
  tabInc
  emit $ "Loc " ++ dupNam ++ " = alloc_node(3);"
  emit $ "set(" ++ dupNam ++ " + 0, term_new(SUB, 0, 0));"
  emit $ "set(" ++ dupNam ++ " + 1, term_new(SUB, 0, 0));"
  emit $ "set(" ++ dupNam ++ " + 2, " ++ valNam ++ ");"
  emit $ dp0Nam ++ " = term_new(DP0, " ++ show lab ++ ", " ++ dupNam ++ " + 0);"
  emit $ dp1Nam ++ " = term_new(DP1, " ++ show lab ++ ", " ++ dupNam ++ " + 0);"
  tabDec
  emit $ "}"
  bind dp0 dp0Nam
  bind dp1 dp1Nam
  compileFastCore book fid bod
compileFastCore book fid (Ctr cid fds) = do
  uid <- fresh
  let ctrName = "ctr" ++ show uid
  let arity = length fds
  emit $ "Loc " ++ ctrName ++ " = alloc_node(" ++ show arity ++ ");"
  fdsT <- mapM (\ (i,fd) -> compileFastCore book fid fd) (zip [0..] fds)
  sequence_ [emit $ "set(" ++ ctrName ++ " + " ++ show i ++ ", " ++ fdT ++ ");" | (i,fdT) <- zip [0..] fdsT]
  return $ "term_new(CTR, u12v2_new(" ++ show cid ++ ", " ++ show arity ++ "), " ++ ctrName ++ ")"
compileFastCore book fid (Mat val css) = do
  uid <- fresh
  let matName = "mat" ++ show uid
  let arity = length css
  emit $ "Loc " ++ matName ++ " = alloc_node(" ++ show (1 + arity) ++ ");"
  valT <- compileFastCore book fid val
  emit $ "set(" ++ matName ++ " + 0, " ++ valT ++ ");"
  cssT <- mapM (\ (i,(_,cs)) -> compileFastCore book fid cs) (zip [0..] css)
  sequence_ [emit $ "set(" ++ matName ++ " + " ++ show (i+1) ++ ", " ++ csT ++ ");" | (i,csT) <- zip [0..] cssT]
  return $ "term_new(MAT, " ++ show arity ++ ", " ++ matName ++ ")"
compileFastCore book fid (U32 val) =
  return $ "term_new(W32, 0, " ++ show (fromIntegral val) ++ ")"
compileFastCore book fid (Op2 opr nu0 nu1) = do
  opxUid <- fresh
  opxNam <- return $ "opx" ++ show opxUid
  retUid <- fresh
  retNam <- return $ "ret" ++ show retUid
  nu0Uid <- fresh
  nu0Nam <- return $ "nu0" ++ show nu0Uid
  nu1Uid <- fresh
  nu1Nam <- return $ "nu1" ++ show nu1Uid
  nu0T <- compileFastCore book fid nu0
  nu1T <- compileFastCore book fid nu1
  emit $ "Term " ++ nu0Nam ++ " = reduce(" ++ nu0T ++ ");"
  emit $ "Term " ++ nu1Nam ++ " = reduce(" ++ nu1T ++ ");"
  emit $ "Term " ++ retNam ++ ";"
  emit $ "if (term_tag(" ++ nu0Nam ++ ") == W32 && term_tag(" ++ nu1Nam ++ ") == W32) {"
  emit $ "  itrs += 2;"
  emit $ "  " ++ retNam ++ " = term_new(W32, 0, term_loc(" ++ nu0Nam ++ ") + term_loc(" ++ nu1Nam ++ "));"
  emit $ "} else {"
  emit $ "  Loc " ++ opxNam ++ " = alloc_node(2);"
  emit $ "  set(" ++ opxNam ++ " + 0, " ++ nu0Nam ++ ");"
  emit $ "  set(" ++ opxNam ++ " + 1, " ++ nu1Nam ++ ");"
  emit $ "  " ++ retNam ++ " = term_new(OPX, " ++ show (fromEnum opr) ++ ", " ++ opxNam ++ ");"
  emit $ "}"
  return $ retNam
compileFastCore book fid (Ref rNam rFid rArg) = do
  uid <- fresh
  let refName = "ref" ++ show uid
  let arity = length rArg
  emit $ "Loc " ++ refName ++ " = alloc_node(" ++ show arity ++ ");"
  argsT <- mapM (\ (i,arg) -> compileFastCore book fid arg) (zip [0..] rArg)
  sequence_ [emit $ "set(" ++ refName ++ " + " ++ show i ++ ", " ++ argT ++ ");" | (i,argT) <- zip [0..] argsT]
  return $ "term_new(REF, u12v2_new(" ++ show rFid ++ ", " ++ show arity ++ "), " ++ refName ++ ")"

-- Compiles a variable in fast mode
compileFastVar :: String -> Compile String
compileFastVar var = do
  bins <- gets bins
  case MS.lookup var bins of
    Just entry -> do
      return entry
    Nothing -> do
      return "<ERR>"

-- Compiles a function using Fast-Mode
compileSlow :: Book -> Word64 -> Core -> [String] -> Compile ()
compileSlow book fid core args = do
  emit $ "Term " ++ idToName book MS.! fid ++ "_f(Term ref) {"
  emit $ "  return " ++ idToName book MS.! fid ++ "_t(ref);"
  emit $ "}"
