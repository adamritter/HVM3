-- //./Type.hs//

module HVML.Parse where

import HVML.Type
import Text.Parsec hiding (State)
import Text.Parsec.String
import qualified Data.Map.Strict as MS

parseCore :: Parser Core
parseCore = do
  spaces
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
      consume "("
      fun <- parseCore
      arg <- parseCore
      consume ")"
      return $ App fun arg
    '{' -> do
      consume "{"
      tm0 <- parseCore
      tm1 <- parseCore
      consume "}"
      return $ Sup tm0 tm1
    '&' -> do
      consume "&"
      consume "{"
      dp0 <- parseName
      dp1 <- parseName
      consume "}"
      consume "="
      val <- parseCore
      bod <- parseCore
      return $ Dup dp0 dp1 val bod
    '@' -> do
      consume "@"
      nam <- parseName
      return $ Ref nam
    _ -> do
      name <- parseName
      return $ Var name

parseName :: Parser String
parseName = spaces >> many1 (alphaNum <|> char '_')

parseDef :: Parser (String, Core)
parseDef = do
  try $ do
    spaces
    consume "@"
  name <- parseName
  spaces
  consume "="
  core <- parseCore
  return (name, core)

parseBook :: Parser Book
parseBook = do
  spaces
  defs <- many parseDef
  return $ MS.fromList defs

doParseCore :: String -> Core
doParseCore code = case parse parseCore "" code of
  Right core -> core
  Left _     -> Era

doParseBook :: String -> Book
doParseBook code = case parse parseBook "" code of
  Right book -> book
  Left _     -> MS.empty

consume :: String -> Parser String
consume str = spaces >> string str
