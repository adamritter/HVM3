-- //./Type.hs//
-- //./Show.hs//

module HVML.Parse where

import Data.Word
import HVML.Show
import HVML.Type
import Text.Parsec hiding (State)
import Text.Parsec.String
import qualified Data.Map.Strict as MS

import Debug.Trace

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

parseBook :: Parser [(String, Core)]
parseBook = do
  spaces
  many parseDef

doParseCore :: String -> Core
doParseCore code = case parse parseCore "" code of
  Right core -> core
  Left _     -> Era

doParseBook :: String -> Book
doParseBook code = case parse parseBook "" code of
  Right defs -> createBook defs
  Left _     -> Book MS.empty MS.empty MS.empty

consume :: String -> Parser String
consume str = spaces >> string str

closeWith :: String -> Parser ()
closeWith str = try $ do
  spaces
  notFollowedBy (string str)

createBook :: [(String, Core)] -> Book
createBook defs = 
  let nameToId' = MS.fromList $ zip (map fst defs) [0..]
      idToName' = MS.fromList $ map (\(k,v) -> (v,k)) $ MS.toList nameToId'
      decorDefs = map (\ (name, core) -> (nameToId' MS.! name, decorateFnIds nameToId' core)) defs
      idToCore' = MS.fromList decorDefs
  in Book idToCore' idToName' nameToId'

decorateFnIds :: MS.Map String Word64 -> Core -> Core
decorateFnIds fids term = case term of
  Ref nam _   -> Ref nam (fids MS.! nam)
  Lam x bod   -> Lam x (decorateFnIds fids bod)
  App f x     -> App (decorateFnIds fids f) (decorateFnIds fids x)
  Sup x y     -> Sup (decorateFnIds fids x) (decorateFnIds fids y)
  Dup x y v b -> Dup x y (decorateFnIds fids v) (decorateFnIds fids b)
  other       -> other

