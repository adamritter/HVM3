module HVM.Lazy.Parse where

import Text.Parsec hiding (State)
import Text.Parsec.String
import HVM.Lazy.Type

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
    _ -> do
      name <- parseName
      return $ Var name

parseName :: Parser String
parseName = spaces >> many1 (alphaNum <|> char '_')

consume str = spaces >> string str

doParseCore :: String -> Core
doParseCore code = case parse parseCore "" code of
  Right core -> core
  Left _     -> Era