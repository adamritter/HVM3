-- //./Type.hs//

module HVML.Parse where

import Control.Monad (foldM, forM)
import Control.Monad.State
import Data.List
import Data.Maybe
import Data.Word
import Debug.Trace
import HVML.Show
import HVML.Type
import Highlight (highlightError)
import System.Console.ANSI
import System.Exit (exitFailure)
import System.IO.Unsafe (unsafePerformIO)
import Text.Parsec hiding (State)
import Text.Parsec.Error
import Text.Parsec.Pos
import Text.Parsec.String
import qualified Data.Map.Strict as MS

-- Core Parsers
-- ------------

data ParserState = ParserState
  { parsedCtrToAri :: MS.Map String Int
  , parsedCtrToCid :: MS.Map String Word64
  }

type ParserM = Parsec String ParserState

parseCore :: ParserM Core
parseCore = do
  skip
  head <- lookAhead anyChar
  case head of
    '*' -> do
      consume "*"
      return Era
    'λ' -> do
      consume "λ"
      vr0 <- parseName
      bod <- parseCore
      return $ Lam vr0 bod
    '(' -> do
      next <- lookAhead (anyChar >> anyChar)
      case next of
        -- '@' -> parseRef
        '+' -> parseOper OP_ADD
        '-' -> parseOper OP_SUB
        '*' -> parseOper OP_MUL
        '/' -> parseOper OP_DIV
        '%' -> parseOper OP_MOD
        '=' -> parseOper OP_EQ
        '!' -> parseOper OP_NE
        '&' -> parseOper OP_AND
        '|' -> parseOper OP_OR
        '^' -> parseOper OP_XOR
        '<' -> do
          next <- lookAhead (anyChar >> anyChar >> anyChar)
          case next of
            '<' -> parseOper OP_LSH
            '=' -> parseOper OP_LTE
            _   -> parseOper OP_LT
        '>' -> do
          next <- lookAhead (anyChar >> anyChar >> anyChar)
          case next of
            '>' -> parseOper OP_RSH
            '=' -> parseOper OP_GTE
            _   -> parseOper OP_GT
        _ -> do
          consume "("
          fun <- parseCore
          args <- many $ do
            closeWith ")"
            parseCore
          char ')'
          return $ foldl App fun args
    '@' -> parseRef
    '&' -> do
      consume "&"
      lab <- read <$> many1 digit
      consume "{"
      tm0 <- parseCore
      tm1 <- parseCore
      consume "}"
      return $ Sup lab tm0 tm1
    '!' -> do
      consume "!"
      skip
      next <- lookAhead anyChar
      case next of
        '&' -> do
          consume "&"
          lab <- read <$> many1 digit
          consume "{"
          dp0 <- parseName
          dp1 <- parseName
          consume "}"
          consume "="
          val <- parseCore
          bod <- parseCore
          return $ Dup lab dp0 dp1 val bod
        '!' -> do
          -- parsing strict 'let'
          consume "!"
          nam <- parseName
          consume "="
          val <- parseCore
          bod <- parseCore
          return $ Let STRI nam val bod
        '^' -> do
          -- parsing parallel 'let'
          consume "^"
          nam <- parseName
          consume "="
          val <- parseCore
          bod <- parseCore
          return $ Let PARA nam val bod
        _ -> do
          -- parsing lazy 'let'
          nam <- parseName
          consume "="
          val <- parseCore
          bod <- parseCore
          return $ Let LAZY nam val bod
    '#' -> parseCtr
    '~' -> parseMat
    '[' -> parseLst
    '\'' -> parseChr
    '"' -> parseStr
    _ -> do
      name <- parseName
      case reads (filter (/= '_') name) of
        [(num, "")] -> return $ U32 (fromIntegral (num :: Integer))
        _           -> return $ Var name

parseRef :: ParserM Core
parseRef = do
  consume "@"
  name <- parseName
  args <- option [] $ do
    try $ string "("
    args <- many $ do
      closeWith ")"
      parseCore
    consume ")"
    return args
  return $ Ref name 0 args

parseCtr :: ParserM Core
parseCtr = do
  consume "#"
  nam <- parseName
  cid <- if length nam == 0
    then return 0
    else do
      cids <- parsedCtrToCid <$> getState
      case MS.lookup nam cids of
        Just id -> return id
        Nothing -> case reads nam of
          [(num, "")] -> return (fromIntegral (num :: Integer))
          otherwise   -> fail $ "Unknown constructor: " ++ nam
  fds <- option [] $ do
    try $ consume "{"
    fds <- many $ do
      closeWith "}"
      parseCore
    consume "}"
    return fds
  return $ Ctr cid fds

parseMat :: ParserM Core
parseMat = do
  consume "~"
  val <- parseCore
  -- Parse mov (external variables)
  mov <- many $ do
    try $ do
      skip
      consume "!"
    key <- parseName
    val <- optionMaybe $ do
      try $ consume "="
      parseCore
    case val of
      Just v  -> return (key, v)
      Nothing -> return (key, Var key)
  consume "{"
  css <- many $ do
    closeWith "}"
    next <- lookAhead anyChar
    -- Parse constructor case
    if next == '#' then do
      consume "#"
      ctr <- parseName
      fds <- option [] $ do
        try $ consume "{"
        fds <- many $ do
          closeWith "}"
          parseName
        consume "}"
        return fds
      consume ":"
      bod <- parseCore
      return (ctr, fds, bod)
    -- Parse numeric case
    else do
      num <- parseName
      case reads num of
        [(n :: Word64, "")] -> do
          consume ":"
          bod <- parseCore
          return (num, [], bod)
        otherwise -> do
          consume ":"
          bod <- parseCore
          return ("+", [num], bod)
  consume "}"
  css <- forM css $ \(ctr, fds, bod) -> do
    cid <- case reads ctr of
      [(num, "")]  -> return $ Left (read num :: Word64)
      _            -> do st <- getState; return $ Right $ fromMaybe maxBound $ MS.lookup ctr (parsedCtrToCid st)
    return (cid, (ctr, fds, bod))
  css <- return $ map snd $ sortOn fst css
  return $ Mat val mov css

parseOper :: Oper -> ParserM Core
parseOper op = do
  consume "("
  consume (operToString op)
  nm0 <- parseCore
  nm1 <- parseCore
  consume ")"
  return $ Op2 op nm0 nm1

parseEscapedChar :: ParserM Char
parseEscapedChar = choice
  [ try $ do
      char '\\'
      c <- oneOf "\\\"nrtbf0/\'"
      return $ case c of
        '\\' -> '\\'
        '/'  -> '/'
        '"'  -> '"'
        '\'' -> '\''
        'n'  -> '\n'
        'r'  -> '\r'
        't'  -> '\t'
        'b'  -> '\b'
        'f'  -> '\f'
        '0'  -> '\0'
  , try $ do
      string "\\u"
      code <- count 4 hexDigit
      return $ toEnum (read ("0x" ++ code) :: Int)
  , noneOf "\"\\"
  ]

parseChr :: ParserM Core
parseChr = do
  skip
  char '\''
  c <- parseEscapedChar
  char '\''
  return $ Chr c

parseStr :: ParserM Core
parseStr = do
  skip
  char '"'
  str <- many (noneOf "\"")
  char '"'
  return $ foldr (\c acc -> Ctr 1 [Chr c, acc]) (Ctr 0 []) str

parseLst :: ParserM Core
parseLst = do
  skip
  char '['
  elems <- many $ do
    closeWith "]"
    parseCore
  char ']'
  return $ foldr (\x acc -> Ctr 1 [x, acc]) (Ctr 0 []) elems

parseName :: ParserM String
parseName = skip >> many (alphaNum <|> char '_' <|> char '$')

parseName1 :: ParserM String
parseName1 = skip >> many1 (alphaNum <|> char '_')

parseDef :: ParserM (String, ([String], Core))
parseDef = do
  try $ do
    skip
    consume "@"
  name <- parseName
  args <- option [] $ do
    try $ string "("
    args <- many $ do
      closeWith ")"
      parseName
    consume ")"
    return args
  skip
  consume "="
  core <- parseCore
  -- trace ("PARSED: " ++ name ++ "(" ++ intercalate "," args ++ ") = " ++ coreToString core) $ return ()
  return (name, (args, core))

parseADT :: ParserM ()
parseADT = do
  try $ do
    skip
    consume "data"
  name <- parseName
  skip
  consume "{"
  constructors <- many parseADTCtr
  consume "}"
  let ctrCids = zip (map fst constructors) [0..]
  let ctrAris = zip (map fst constructors) (map (fromIntegral . length . snd) constructors)
  modifyState (\s -> s { parsedCtrToCid = MS.union (MS.fromList ctrCids) (parsedCtrToCid s),
                         parsedCtrToAri = MS.union (MS.fromList ctrAris) (parsedCtrToAri s) })

parseADTCtr :: ParserM (String, [String])
parseADTCtr = do
  skip
  consume "#"
  name <- parseName
  fields <- option [] $ do
    try $ consume "{"
    fds <- many $ do
      closeWith "}"
      parseName
    skip
    consume "}"
    return fds
  skip
  return (name, fields)

parseBook :: ParserM [(String, ([String], Core))]
parseBook = do
  skip
  many parseADT
  defs <- many parseDef
  skip
  eof
  return defs

doParseCore :: String -> IO Core
doParseCore code = case runParser parseCore (ParserState MS.empty MS.empty) "" code of
  Right core -> do
    return $ core
  Left  err  -> do
    showParseError "" code err
    return $ Ref "⊥" 0 []

doParseBook :: String -> IO Book
doParseBook code = case runParser parseBookWithState (ParserState MS.empty MS.empty) "" code of
  Right (defs, st) -> do
    return $ createBook defs (parsedCtrToCid st) (parsedCtrToAri st)
  Left err -> do
    showParseError "" code err
    return $ Book MS.empty MS.empty MS.empty MS.empty MS.empty
  where
    parseBookWithState :: ParserM ([(String, ([String], Core))], ParserState)
    parseBookWithState = do
      defs <- parseBook
      st   <- getState
      return (defs, st)

-- Helper Parsers
-- --------------

consume :: String -> ParserM String
consume str = spaces >> string str

closeWith :: String -> ParserM ()
closeWith str = try $ do
  spaces
  notFollowedBy (string str)

skip :: ParserM ()
skip = skipMany (parseSpace <|> parseComment) where
  parseSpace = (try $ do
    space
    return ()) <?> "space"
  parseComment = (try $ do
    string "//"
    skipMany (noneOf "\n")
    char '\n'
    return ()) <?> "Comment"

-- Adjusting
-- ---------

createBook :: [(String, ([String], Core))] -> MS.Map String Word64 -> MS.Map String Int -> Book
createBook defs ctrToCid ctrToAri =
  let nameToId' = MS.fromList $ zip (map fst defs) [0..]
      idToName' = MS.fromList $ map (\(k,v) -> (v,k)) $ MS.toList nameToId'
      idToFunc' = MS.fromList $ map (\ (name, (args, core)) -> (mget nameToId' name, (args, lexify (setRefIds nameToId' core)))) defs
  in Book idToFunc' idToName' nameToId' ctrToAri ctrToCid

-- Adds the function id to Ref constructors
setRefIds :: MS.Map String Word64 -> Core -> Core
setRefIds fids term = case term of
  Var nam       -> Var nam
  Let m x v b   -> Let m x (setRefIds fids v) (setRefIds fids b)
  Lam x bod     -> Lam x (setRefIds fids bod)
  App f x       -> App (setRefIds fids f) (setRefIds fids x)
  Sup l x y     -> Sup l (setRefIds fids x) (setRefIds fids y)
  Dup l x y v b -> Dup l x y (setRefIds fids v) (setRefIds fids b)
  Ctr cid fds   -> Ctr cid (map (setRefIds fids) fds)
  Mat x mov css -> Mat (setRefIds fids x) (map (\ (k,v) -> (k, setRefIds fids v)) mov) (map (\ (ctr,fds,cs) -> (ctr, fds, setRefIds fids cs)) css)
  Op2 op x y    -> Op2 op (setRefIds fids x) (setRefIds fids y)
  U32 n         -> U32 n
  Chr c         -> Chr c
  Era           -> Era
  Ref nam _ arg -> case MS.lookup nam fids of
    Just fid -> Ref nam fid (map (setRefIds fids) arg)
    Nothing  -> unsafePerformIO $ do
      putStrLn $ "error:unbound-ref @" ++ nam
      exitFailure

-- Gives unique names to lexically scoped vars, unless they start with '$'.
-- Example: `λx λt (t λx(x) x)` will read as `λx0 λt1 (t1 λx2(x2) x0)`.
lexify :: Core -> Core
lexify term = evalState (go term MS.empty) 0 where
  fresh :: String -> State Int String
  fresh nam@('$':_) = return $ nam
  fresh nam         = do i <- get; put (i+1); return $ nam++"$"++show i

  extend :: String -> String -> MS.Map String String -> State Int (MS.Map String String)
  extend old@('$':_) new ctx = return $ ctx
  extend old         new ctx = return $ MS.insert old new ctx

  go :: Core -> MS.Map String String -> State Int Core
  go term ctx = case term of
    Var nam -> 
      return $ Var (MS.findWithDefault nam nam ctx)
    Ref nam fid arg -> do
      arg <- mapM (\x -> go x ctx) arg
      return $ Ref nam fid arg
    Let mod nam val bod -> do
      val  <- go val ctx
      nam' <- fresh nam
      ctx  <- extend nam nam' ctx
      bod  <- go bod ctx
      return $ Let mod nam' val bod
    Lam nam bod -> do
      nam' <- fresh nam
      ctx  <- extend nam nam' ctx
      bod  <- go bod ctx
      return $ Lam nam' bod
    App fun arg -> do
      fun <- go fun ctx
      arg <- go arg ctx
      return $ App fun arg
    Sup lab tm0 tm1 -> do
      tm0 <- go tm0 ctx
      tm1 <- go tm1 ctx
      return $ Sup lab tm0 tm1
    Dup lab dp0 dp1 val bod -> do
      val  <- go val ctx
      dp0' <- fresh dp0
      dp1' <- fresh dp1
      ctx  <- extend dp0 dp0' ctx
      ctx  <- extend dp1 dp1' ctx
      bod  <- go bod ctx
      return $ Dup lab dp0' dp1' val bod
    Ctr cid fds -> do
      fds <- mapM (\x -> go x ctx) fds
      return $ Ctr cid fds
    Mat val mov css -> do
      val' <- go val ctx
      mov' <- forM mov $ \ (k,v) -> do
        k' <- fresh k
        v  <- go v ctx
        return $ (k', v)
      css' <- forM css $ \ (ctr,fds,bod) -> do
        fds' <- mapM fresh fds
        ctx  <- foldM (\ ctx (fd,fd') -> extend fd fd' ctx) ctx (zip fds fds')
        ctx  <- foldM (\ ctx ((k,_),(k',_)) -> extend k k' ctx) ctx (zip mov mov')
        bod <- go bod ctx
        return (ctr, fds', bod)
      return $ Mat val' mov' css'
    Op2 op nm0 nm1 -> do
      nm0 <- go nm0 ctx
      nm1 <- go nm1 ctx
      return $ Op2 op nm0 nm1
    U32 n -> 
      return $ U32 n
    Chr c ->
      return $ Chr c
    Era -> 
      return Era

-- Errors
-- ------

-- Error handling
extractExpectedTokens :: ParseError -> String
extractExpectedTokens err =
    let expectedMsgs = [msg | Expect msg <- errorMessages err, msg /= "space", msg /= "Comment"]
    in intercalate " | " expectedMsgs

showParseError :: String -> String -> ParseError -> IO ()
showParseError filename input err = do
  let pos = errorPos err
  let lin = sourceLine pos
  let col = sourceColumn pos
  let errorMsg = extractExpectedTokens err
  putStrLn $ setSGRCode [SetConsoleIntensity BoldIntensity] ++ "\nPARSE_ERROR" ++ setSGRCode [Reset]
  putStrLn $ "- expected: " ++ errorMsg
  putStrLn $ "- detected:"
  putStrLn $ highlightError (lin, col) (lin, col + 1) input
  putStrLn $ setSGRCode [SetUnderlining SingleUnderline] ++ filename ++ setSGRCode [Reset]
