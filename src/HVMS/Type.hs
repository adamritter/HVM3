module HVMS.Type where

import Data.Word
import Foreign.C.String
import qualified Data.Map.Strict as MS


-- Core Types
-- ----------

-- A Term is a tree of IN nodes, ending in variables (aux wires)
data PCore
  = PVar String
  | PRef String
  | PNul
  | PLam NCore PCore
  | PSup PCore PCore
  | PU32 Word32
  deriving (Show, Eq)

data NCore
  = NSub String
  | NEra
  | NApp PCore NCore
  | POp2 Oper  PCore NCore
  | NDup NCore NCore
  deriving (Show, Eq)

data Oper
  = OP_ADD | OP_SUB | OP_MUL | OP_DIV
  | OP_MOD | OP_EQ  | OP_NE  | OP_LT
  | OP_GT  | OP_LTE | OP_GTE | OP_AND
  | OP_OR  | OP_XOR | OP_LSH | OP_RSH
  deriving (Show, Eq, Enum)

-- A Redex is a pair of Terms (trees connected by their main ports)
type Dex = (NCore, PCore)

-- A Bag is a list of redexes
type Bag = [Dex]

-- A Net is a Bag, plus a root Term
data Net = Net
  { netRoot :: PCore
  , netBag  :: Bag
  } deriving (Show, Eq)

-- A Book is a set of definitions
data Book = Book
  { defs :: MS.Map String Net
  } deriving (Show, Eq)

-- Runtime Types
-- -------------

type Tag  = Word8
type Lab  = Word32
type Loc  = Word32
type Term = Word64

-- Runtime constants
_VAR_, _SUB_, _NUL_, _ERA_, _LAM_, _APP_, _SUP_, _DUP_, _REF_, _OPX_, _OPY_, _W32_ :: Tag
_VAR_ = 0x01
_SUB_ = 0x02
_NUL_ = 0x03
_ERA_ = 0x04
_LAM_ = 0x05
_APP_ = 0x06
_SUP_ = 0x07
_DUP_ = 0x08
_REF_ = 0x09
_OPX_ = 0x0A
_OPY_ = 0x0B
_W32_ = 0x0C

_VOID_ :: Term
_VOID_ = 0x0

-- FFI imports
foreign import ccall unsafe "Runtime.c hvm_init"
  hvmInit :: IO ()

foreign import ccall unsafe "Runtime.c hvm_free"
  hvmFree :: IO ()

foreign import ccall unsafe "Runtime.c term_new"
  termNew :: Tag -> Lab -> Loc -> Term

foreign import ccall unsafe "Runtime.c term_tag"
  termTag :: Term -> Tag

foreign import ccall unsafe "Runtime.c term_lab"
  termLab :: Term -> Lab

foreign import ccall unsafe "Runtime.c term_loc"
  termLoc :: Term -> Loc

foreign import ccall unsafe "Runtime.c def_new"
  defNew :: CString -> IO ()

foreign import ccall unsafe "Runtime.c swap"
  swap :: Loc -> Term -> IO Term

foreign import ccall unsafe "Runtime.c get"
  get :: Loc -> IO Term

foreign import ccall unsafe "Runtime.c set"
  set :: Loc -> Term -> IO ()

foreign import ccall unsafe "Runtime.c rbag_push"
  rbagPush :: Term -> Term -> IO ()

foreign import ccall unsafe "Runtime.c rbag_ini"
  rbagIni :: IO Loc

foreign import ccall unsafe "Runtime.c rbag_end"
  rbagEnd :: IO Loc

-- foreign import ccall unsafe "Runtime.c take"
--   take :: Loc -> IO Term

foreign import ccall unsafe "Runtime.c alloc_node"
  allocNode :: Word64 -> IO Loc

foreign import ccall unsafe "Runtime.c inc_itr"
  incItr :: IO Word64

foreign import ccall unsafe "Runtime.c normalize"
  normalize :: Term -> IO Term

foreign import ccall unsafe "Runtime.c dump_buff"
  dumpBuff :: IO ()
