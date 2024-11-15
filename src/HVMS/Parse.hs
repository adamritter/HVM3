module HVMS.Parse where

import Text.Parsec
import Text.Parsec.String
import HVMS.Type

import Debug.Trace

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

-- Utilities
-- ---------

peekNextChar :: Parser Char
peekNextChar = spaces >> lookAhead anyChar

parseName :: Parser String
parseName = spaces >> many1 (alphaNum <|> char '_')

consume :: String -> Parser String
consume str = spaces >> string str

-- Main Entry Points
-- ----------------

doParseNet :: String -> Either String Net
doParseNet code = case parse parseNet "" code of
  Right net -> Right net
  Left  err -> Left  (show err)
