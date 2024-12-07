module HVMS.Parse where

import Text.Parsec
import Text.Parsec.String
import HVMS.Type

import Debug.Trace
import qualified Data.Map.Strict as MS

-- Core Parser
-- ----------

parsePCore :: Parser PCore
parsePCore = do
  head <- peekNextChar
  case head of
    '*' -> do
      consume "*"
      return PNul
    '(' -> do
      consume "("
      var <- parseNCore
      bod <- parsePCore
      consume ")"
      return $ PLam var bod
    '{' -> do
      consume "{"
      tm1 <- parsePCore
      tm2 <- parsePCore
      consume "}"
      return $ PSup tm1 tm2
    '@' -> do
      consume "@"
      name <- parseName
      return $ PRef name
    _ -> do
      name <- parseName
      return $ PVar name

parseNCore :: Parser NCore
parseNCore = do
  head <- peekNextChar
  case head of
    '*' -> do
      consume "*"
      return NEra
    '(' -> do
      consume "("
      arg <- parsePCore
      ret <- parseNCore
      consume ")"
      return $ NApp arg ret
    '{' -> do
      consume "{"
      dp1 <- parseNCore
      dp2 <- parseNCore
      consume "}"
      return $ NDup dp1 dp2
    _ -> do
      name <- parseName
      return $ NSub name

parseDex :: Parser Dex
parseDex = do
  consume "&"
  neg <- parseNCore
  consume "~"
  pos <- parsePCore
  return (neg, pos)

parseBag :: Parser Bag
parseBag = do
  head <- try peekNextChar <|> return ' '
  case head of
    '&' -> do
      dex <- parseDex
      rest <- parseBag
      return (dex : rest)
    _ -> return []

parseNet :: Parser Net
parseNet = do
  rot <- parsePCore
  bag <- parseBag
  return $ Net rot bag

parseDef :: Parser (String, Net)
parseDef = do
  consume "@"
  name <- parseName
  consume "="
  net <- parseNet
  spaces
  return (name, net)

parseBook :: Parser Book
parseBook = do
  defs <- many parseDef
  spaces
  eof
  return $ Book (MS.fromList defs)

-- Utilities
-- ---------

peekNextChar :: Parser Char
peekNextChar = spaces >> lookAhead anyChar

parseName :: Parser String
parseName = spaces >> many1 (alphaNum <|> char '_')

consume :: String -> Parser String
consume str = spaces >> string str

-- Main Entry Point
-- ----------------

doParseBook :: String -> Either String Book
doParseBook code = case parse parseBook "" code of
  Right net -> Right net
  Left  err -> Left  (show err)
