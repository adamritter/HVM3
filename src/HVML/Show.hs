module HVML.Show where

import Data.Char (intToDigit)
import Data.Word
import HVML.Type
import Numeric (showIntAtBase)

-- Core Stringification
-- --------------------

coreToString :: Core -> String
coreToString (Var nam)             = nam
coreToString Era                   = "*"
coreToString (Lam vr0 bod)         = "λ" ++ vr0 ++ " " ++ coreToString bod
coreToString (App fun arg)         = "(" ++ coreToString fun ++ " " ++ coreToString arg ++ ")"
coreToString (Sup tm0 tm1)         = "{" ++ coreToString tm0 ++ " " ++ coreToString tm1 ++ "}"
coreToString (Dup dp0 dp1 val bod) = "&{" ++ dp0 ++ " " ++ dp1 ++ "} = " ++ coreToString val ++ " " ++ coreToString bod

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
