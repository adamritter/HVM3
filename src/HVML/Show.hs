module HVML.Show where

import Control.Applicative ((<|>))
import Control.Monad.State
import Data.Char (intToDigit)
import Data.List
import Data.Word
import HVML.Type
import Numeric (showIntAtBase)

-- Core Stringification
-- --------------------

coreToString :: Core -> String
coreToString core = case pretty core of
  Just str -> str
  Nothing -> case core of
    Var nam ->
      nam
    Era ->
      "*"
    Lam vr0 bod ->
      let bod' = coreToString bod in
      "λ" ++ vr0 ++ " " ++ bod'
    App fun arg ->
      let fun' = coreToString fun in
      let arg' = coreToString arg in
      "(" ++ fun' ++ " " ++ arg' ++ ")"
    Sup lab tm0 tm1 ->
      let tm0' = coreToString tm0 in
      let tm1' = coreToString tm1 in
      "&" ++ show lab ++ "{" ++ tm0' ++ " " ++ tm1' ++ "}"
    Dup lab dp0 dp1 val bod ->
      let val' = coreToString val in
      let bod' = coreToString bod in
      "! &" ++ show lab ++ "{" ++ dp0 ++ " " ++ dp1 ++ "} = " ++ val' ++ "\n" ++ bod'
    Ref nam fid arg ->
      let arg' = intercalate " " (map coreToString arg) in
      "@" ++ nam ++ "(" ++ arg' ++ ")"
    Ctr cid fds ->
      let fds' = unwords (map coreToString fds) in
      "#" ++ show cid ++ "{" ++ fds' ++ "}"
    Mat val mov css ->
      let val' = coreToString val in
      let mov' = concatMap (\ (k,v) -> " !" ++ k ++ "=" ++ coreToString v) mov in
      let css' = unwords [ctr ++ "{" ++ unwords fds ++ "}:" ++ coreToString bod | (ctr, fds, bod) <- css] in
      "(~" ++ val' ++ mov' ++ " {" ++ css' ++ "})"
    U32 val ->
      show val
    Chr val ->
      "'" ++ [val] ++ "'"
    Op2 opr nm0 nm1 ->
      let nm0' = coreToString nm0 in
      let nm1' = coreToString nm1 in
      "(" ++ operToString opr ++ " " ++ nm0' ++ " " ++ nm1' ++ ")"
    Let mod nam val bod ->
      let val' = coreToString val in
      let bod' = coreToString bod in
      "! " ++ modeToString mod ++ nam ++ " = " ++ val' ++ " " ++ bod'

operToString :: Oper -> String
operToString OP_ADD = "+"
operToString OP_SUB = "-"
operToString OP_MUL = "*"
operToString OP_DIV = "/"
operToString OP_MOD = "%"
operToString OP_EQ  = "=="
operToString OP_NE  = "!="
operToString OP_LT  = "<"
operToString OP_GT  = ">"
operToString OP_LTE = "<="
operToString OP_GTE = ">="
operToString OP_AND = "&"
operToString OP_OR  = "|"
operToString OP_XOR = "^"
operToString OP_LSH = "<<"
operToString OP_RSH = ">>"

modeToString LAZY = ""
modeToString STRI = "."
modeToString PARA = "^"

-- Runtime Stringification
-- -----------------------

tagToString :: Tag -> String
tagToString t = show (tagT t)

labToString :: Word64 -> String
labToString loc = padLeft (showHex loc) 6 '0'

locToString :: Word64 -> String
locToString loc = padLeft (showHex loc) 9 '0'

termToString :: Term -> String
termToString term =
  let tag = tagToString (termTag term)
      lab = labToString (termLab term)
      loc = locToString (termLoc term)
  in "term_new(" ++ tag ++ ",0x" ++ lab ++ ",0x" ++ loc ++ ")"

-- Pretty Printers
-- ---------------

pretty :: Core -> Maybe String
pretty core = prettyStr core <|> prettyLst core

prettyStr :: Core -> Maybe String
prettyStr (Ctr 0 []) = Just "\"\""
prettyStr (Ctr 1 [Chr h, t]) = do
  rest <- prettyStr t
  return $ "\"" ++ h : tail rest
prettyStr _ = Nothing

prettyLst :: Core -> Maybe String
prettyLst (Ctr 0 []) = Just "[]"
prettyLst (Ctr 1 [x, xs]) = do
  rest <- prettyLst xs
  return $ "[" ++ coreToString x ++ if rest == "[]" then "]" else " " ++ tail rest
prettyLst _ = Nothing

-- Dumping
-- -------

dumpHeapRange :: Word64 -> Word64 -> HVM [(Word64, Term)]
dumpHeapRange ini len =
  if ini < len then do
    head <- got ini
    tail <- dumpHeapRange (ini + 1) len
    if head == 0
      then return tail
      else return ((ini, head) : tail)
  else return []

dumpHeap :: HVM ([(Word64, Term)], Word64)
dumpHeap = do
  len <- getLen
  itr <- getItr
  terms <- dumpHeapRange 0 len
  return (terms, itr)

heapToString :: ([(Word64, Term)], Word64) -> String
heapToString (terms, itr) = 
  "set_itr(0x" ++ padLeft (showHex itr) 9 '0' ++ ");\n" ++
  foldr (\(k,v) txt ->
    let addr = padLeft (showHex k) 9 '0'
        term = termToString v
    in "set(0x" ++ addr ++ ", " ++ term ++ ");\n" ++ txt) "" terms

padLeft :: String -> Int -> Char -> String
padLeft str n c = replicate (n - length str) c ++ str

showHex :: Word64 -> String
showHex x = showIntAtBase 16 intToDigit (fromIntegral x) ""
