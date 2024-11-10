-- //./Type.hs//
-- //./Show.hs//

module HVML.Parse where

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

parseCore :: Parser Core
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
          arg <- parseCore
          consume ")"
          return $ App fun arg
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
    '@' -> do
      consume "@"
      nam <- parseName
      return $ Ref nam 0
    '#' -> do
      consume "#"
      cid <- read <$> many1 digit
      consume "{"
      fds <- many $ do
        closeWith "}"
        parseCore
      consume "}"
      return $ Ctr cid fds
    '~' -> do
      consume "~"
      val <- parseCore
      consume "{"
      css <- many $ do
        closeWith "}"
        parseCore
      consume "}"
      return $ Mat val css
    _ -> do
      name <- parseName
      case reads name of
        [(num, "")] -> return $ U32 (fromIntegral (num :: Integer))
        _           -> return $ Var name

parseOper :: Oper -> Parser Core
parseOper op = do
  consume "("
  consume (operToString op)
  nm0 <- parseCore
  nm1 <- parseCore
  consume ")"
  return $ Op2 op nm0 nm1

parseName :: Parser String
parseName = skip >> many1 (alphaNum <|> char '_')

parseDef :: Parser (String, Core)
parseDef = do
  try $ do
    skip
    consume "@"
  name <- parseName
  skip
  consume "="
  core <- parseCore
  return (name, core)

parseBook :: Parser [(String, Core)]
parseBook = do
  skip
  defs <- many parseDef
  skip
  eof
  return defs

doParseCore :: String -> IO Core
doParseCore code = case parse parseCore "" code of
  Right core -> return $ core
  Left  err  -> do
    showParseError "" code err
    return $ Ref "⊥" 0

doParseBook :: String -> IO Book
doParseBook code = case parse parseBook "" code of
  Right defs -> return $ createBook defs
  Left  err  -> do
    showParseError "" code err
    return $ Book MS.empty MS.empty MS.empty

-- Helper Parsers
-- --------------

consume :: String -> Parser String
consume str = spaces >> string str

closeWith :: String -> Parser ()
closeWith str = try $ do
  spaces
  notFollowedBy (string str)

skip :: Parser ()
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

createBook :: [(String, Core)] -> Book
createBook defs = 
  let nameToId' = MS.fromList $ zip (map fst defs) [0..]
      idToName' = MS.fromList $ map (\(k,v) -> (v,k)) $ MS.toList nameToId'
      decorDefs = map (\ (name, core) -> (nameToId' MS.! name, decorateFnIds nameToId' core)) defs
      idToCore' = MS.fromList decorDefs
  in Book idToCore' idToName' nameToId'

decorateFnIds :: MS.Map String Word64 -> Core -> Core
decorateFnIds fids term = case term of
  Ref nam _     -> Ref nam (fids MS.! nam)
  Lam x bod     -> Lam x (decorateFnIds fids bod)
  App f x       -> App (decorateFnIds fids f) (decorateFnIds fids x)
  Sup l x y     -> Sup l (decorateFnIds fids x) (decorateFnIds fids y)
  Dup l x y v b -> Dup l x y (decorateFnIds fids v) (decorateFnIds fids b)
  other         -> other

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
