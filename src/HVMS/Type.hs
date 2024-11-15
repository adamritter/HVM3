module HVMS.Type where

import Data.Word

-- Core Types
-- ----------

-- A Term is a tree of IN nodes, ending in variables (aux wires)
data PCore
  = PVar String
  | PNul
  | PLam NCore PCore
  | PSup PCore PCore
  deriving (Show, Eq)

data NCore
  = NSub String
  | NEra
  | NApp PCore NCore
  | NDup NCore NCore
  deriving (Show, Eq)

-- A Redex is a pair of Terms (trees connected by their main ports)
type Dex = (NCore, PCore)

-- A Bag is a list of redexes
type Bag = [Dex]

-- A Net is a Bag, plus a root Term
data Net = Net
  { netRoot :: PCore
  , netBag  :: Bag
  } deriving (Show, Eq)

-- Runtime Types
-- -------------

type Tag  = Word64
type Lab  = Word64
type Loc  = Word64
type Term = Word64

-- Runtime constants
_VAR_, _SUB_, _NUL_, _ERA_, _LAM_, _APP_, _SUP_, _DUP_ :: Tag
_VAR_ = 0x01
_SUB_ = 0x02
_NUL_ = 0x03
_ERA_ = 0x04
_LAM_ = 0x05
_APP_ = 0x06
_SUP_ = 0x07
_DUP_ = 0x08

_VOID_ :: Term
_VOID_ = 0x00000000_000000_00

_RBAG_ :: Word64
_RBAG_ = 0x1_0000_0000

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

-- foreign import ccall unsafe "Runtime.c term_key"
--   termKey :: Term -> Loc

foreign import ccall unsafe "Runtime.c swap"
  swap :: Loc -> Term -> IO Term

foreign import ccall unsafe "Runtime.c got"
  got :: Loc -> IO Term

foreign import ccall unsafe "Runtime.c set"
  set :: Loc -> Term -> IO ()

-- foreign import ccall unsafe "Runtime.c take"
--   take :: Loc -> IO Term

foreign import ccall unsafe "Runtime.c alloc_node"
  allocNode :: Word64 -> IO Word64

foreign import ccall unsafe "Runtime.c inc_itr"
  incItr :: IO Word64

foreign import ccall unsafe "Runtime.c normal"
  normal :: Term -> IO Term
