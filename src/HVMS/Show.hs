module HVMS.Show where

import Data.Word
import Numeric (showHex)
import HVMS.Type

-- Core to String
-- -------------

pcoreToString :: PCore -> String
pcoreToString (PVar nam)     = nam
pcoreToString PNul           = "*"
pcoreToString (PLam var bod) = "(" ++ ncoreToString var ++ " " ++ pcoreToString bod ++ ")"
pcoreToString (PSup t1 t2)   = "{" ++ pcoreToString t1 ++ " " ++ pcoreToString t2 ++ "}"

ncoreToString :: NCore -> String
ncoreToString (NSub nam)     = nam
ncoreToString NEra           = "*"
ncoreToString (NApp arg ret) = "(" ++ pcoreToString arg ++ " " ++ ncoreToString ret ++ ")"
ncoreToString (NDup d1 d2)   = "{" ++ ncoreToString d1 ++ " " ++ ncoreToString d2 ++ "}"

dexToString :: Dex -> String
dexToString (neg, pos) = ncoreToString neg ++ " ~ " ++ pcoreToString pos

bagToString :: Bag -> String
bagToString [] = ""
bagToString (dex:rest) = "& " ++ dexToString dex ++ "\n" ++ bagToString rest

netToString :: Net -> String
netToString (Net rot bag) = pcoreToString rot ++ "\n" ++ bagToString bag

-- Runtime to String
-- ----------------

tagToString :: Tag -> String
tagToString tag
  | tag == _VAR_ = "VAR"
  | tag == _SUB_ = "SUB"
  | tag == _NUL_ = "NUL"
  | tag == _ERA_ = "ERA"
  | tag == _LAM_ = "LAM"
  | tag == _APP_ = "APP"
  | tag == _SUP_ = "SUP"
  | tag == _DUP_ = "DUP"
  | otherwise    = "???"

labToString :: Lab -> String
labToString lab = padLeft (showHex lab "") 6 '0'

locToString :: Loc -> String
locToString loc = padLeft (showHex loc "") 9 '0'

termToString :: Term -> String
termToString term = tagToString (termTag term) ++ ":" ++ labToString (termLab term) ++ ":" ++ locToString (termLoc term)

-- Utilities
-- ---------

padLeft :: String -> Int -> Char -> String
padLeft str n c = replicate (n - length str) c ++ str
