-- //./Type.hs//
-- //./Show.hs//

module HVML.Parse where

import Control.Monad.State
import Data.List
import Data.Maybe
import Data.Word
import Debug.Trace
import HVML.Show
import HVML.Type
import Highlight (highlightError)
import System.Console.ANSI
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
  consume "{"
  css <- many $ do
    closeWith "}"
    next <- lookAhead anyChar
    case next of
      '#' -> do
        -- Parse ADT constructor case
        consume "#"
        name <- parseName
        cids <- parsedCtrToCid <$> getState
        aris <- parsedCtrToAri <$> getState
        ari  <- case MS.lookup name aris of
          Just ari -> return ari
          Nothing  -> return (-1)
        cid  <- case MS.lookup name cids of
          Just id -> return id
          Nothing -> fail $ "Unknown constructor: " ++ name
        consume ":"
        cas <- parseCore
        return (cid, (ari, cas))
      _ -> do
        -- Parse U32 or named case
        name <- parseName
        cid <- case reads name of
          [(num, "")] -> return (fromIntegral (num :: Integer))
          otherwise   -> return 0xFFFFFFFF
        consume ":"
        cas <- if cid == 0xFFFFFFFF
          then do
            body <- parseCore
            return $ Lam name body
          else do
            parseCore
        return (cid, (-1, cas))
  consume "}"
  let sortedCss = map snd $ sortOn fst css
  return $ Mat val sortedCss

parseOper :: Oper -> ParserM Core
parseOper op = do
  consume "("
  consume (operToString op)
  nm0 <- parseCore
  nm1 <- parseCore
  consume ")"
  return $ Op2 op nm0 nm1

parseName :: ParserM String
parseName = skip >> many (alphaNum <|> char '_' <|> char '$')

parseName1 :: ParserM String
parseName1 = skip >> many1 (alphaNum <|> char '_')

-- TODO: update the syntax of definitions, from '@foo x y z = body' to '@foo(x,y,z) = body'. update the trace too
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
  Right core -> return $ core
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
      idToFunc' = MS.fromList $ map (\ (name, (args, core)) -> (nameToId' MS.! name, (args, lexify (setRefIds nameToId' core)))) defs
  in Book idToFunc' idToName' nameToId' ctrToAri ctrToCid

-- Adds the function id to Ref constructors
setRefIds :: MS.Map String Word64 -> Core -> Core
setRefIds fids term = case term of
  Var nam       -> Var nam
  Ref nam _ arg -> Ref nam (fids MS.! nam) (map (setRefIds fids) arg)
  Let m x v b   -> Let m x (setRefIds fids v) (setRefIds fids b)
  Lam x bod     -> Lam x (setRefIds fids bod)
  App f x       -> App (setRefIds fids f) (setRefIds fids x)
  Sup l x y     -> Sup l (setRefIds fids x) (setRefIds fids y)
  Dup l x y v b -> Dup l x y (setRefIds fids v) (setRefIds fids b)
  Ctr cid fds   -> Ctr cid (map (setRefIds fids) fds)
  Mat x css     -> Mat (setRefIds fids x) (map (\ (ar,cs) -> (ar, setRefIds fids cs)) css)
  Op2 op x y    -> Op2 op (setRefIds fids x) (setRefIds fids y)
  U32 n         -> U32 n
  Era           -> Era

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
    Mat val css -> do
      val <- go val ctx
      css <- mapM (\(ar, cs) -> do
        cs <- go cs ctx
        return (ar, cs)) css
      return $ Mat val css
    Op2 op nm0 nm1 -> do
      nm0 <- go nm0 ctx
      nm1 <- go nm1 ctx
      return $ Op2 op nm0 nm1
    U32 n -> 
      return $ U32 n
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
