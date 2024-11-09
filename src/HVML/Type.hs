-- //./Runtime.c//

module HVML.Type where

import Data.Word
import Data.Map.Strict as MS
import Foreign.Ptr

-- Core Types
-- ----------

data Core
  = Var String
  | Era
  | Lam String Core
  | App Core Core
  | Sup Core Core
  | Dup String String Core Core
  | Ref String Word64
  | Ctr Word64 [Core]
  | Mat Core [Core]
  deriving (Show, Eq)

data Book = Book
  { idToCore :: MS.Map Word64 Core
  , idToName :: MS.Map Word64 String
  , nameToId :: MS.Map String Word64
  } deriving (Show, Eq)

-- Runtime Types
-- -------------

type Tag  = Word64
type Lab  = Word64
type Loc  = Word64
type Term = Word64

data TAG
  = DP0
  | DP1
  | VAR
  | APP
  | ERA
  | LAM
  | SUP
  | SUB
  | REF
  | CTR
  | MAT
  deriving (Eq, Show)

type HVM = IO

-- C Functions
-- -----------

foreign import ccall unsafe "Runtime.c hvm_init"
  hvmInit :: IO ()

foreign import ccall unsafe "Runtime.c hvm_free"
  hvmFree :: IO ()

foreign import ccall unsafe "Runtime.c alloc_node"
  allocNode :: Word64 -> IO Word64

foreign import ccall unsafe "Runtime.c set"
  set :: Word64 -> Term -> IO ()

foreign import ccall unsafe "Runtime.c got"
  got :: Word64 -> IO Term

foreign import ccall unsafe "Runtime.c take"
  take :: Word64 -> IO Term

foreign import ccall unsafe "Runtime.c term_new"
  termNew :: Tag -> Lab -> Loc -> Term

foreign import ccall unsafe "Runtime.c term_tag"
  termTag :: Term -> Tag

foreign import ccall unsafe "Runtime.c term_lab"
  termLab :: Term -> Lab

foreign import ccall unsafe "Runtime.c term_loc"
  termLoc :: Term -> Loc

foreign import ccall unsafe "Runtime.c term_key"
  termKey :: Term -> Loc

foreign import ccall unsafe "Runtime.c get_len"
  getLen :: IO Word64

foreign import ccall unsafe "Runtime.c get_itr"
  getItr :: IO Word64

foreign import ccall unsafe "Runtime.c inc_itr"
  incItr :: IO Word64

foreign import ccall unsafe "Runtime.c reduce"
  reduceC :: Term -> IO Term

foreign import ccall unsafe "Runtime.c reduce_app_era"
  reduceAppEra :: Term -> Term -> IO Term

foreign import ccall unsafe "Runtime.c reduce_app_lam"
  reduceAppLam :: Term -> Term -> IO Term

foreign import ccall unsafe "Runtime.c reduce_app_sup"
  reduceAppSup :: Term -> Term -> IO Term

foreign import ccall unsafe "Runtime.c reduce_app_ctr"
  reduceAppCtr :: Term -> Term -> IO Term

foreign import ccall unsafe "Runtime.c reduce_dup_era"
  reduceDupEra :: Term -> Term -> IO Term

foreign import ccall unsafe "Runtime.c reduce_dup_lam"
  reduceDupLam :: Term -> Term -> IO Term

foreign import ccall unsafe "Runtime.c reduce_dup_sup"
  reduceDupSup :: Term -> Term -> IO Term

foreign import ccall unsafe "Runtime.c reduce_dup_ctr"
  reduceDupCtr :: Term -> Term -> IO Term

foreign import ccall unsafe "Runtime.c reduce_mat_era"
  reduceMatEra :: Term -> Term -> IO Term

foreign import ccall unsafe "Runtime.c reduce_mat_lam"
  reduceMatLam :: Term -> Term -> IO Term

foreign import ccall unsafe "Runtime.c reduce_mat_sup"
  reduceMatSup :: Term -> Term -> IO Term

foreign import ccall unsafe "Runtime.c reduce_mat_ctr"
  reduceMatCtr :: Term -> Term -> IO Term

foreign import ccall unsafe "Runtime.c hvm_define"
  hvmDefine :: Word64 -> FunPtr (IO Term) -> IO ()

foreign import ccall unsafe "Runtime.c hvm_get_state"
  hvmGetState :: IO (Ptr ())

foreign import ccall unsafe "Runtime.c hvm_set_state"
  hvmSetState :: Ptr () -> IO ()

foreign import ccall unsafe "Runtime.c u12v2_new"
  u12v2New :: Word64 -> Word64 -> Word64

foreign import ccall unsafe "Runtime.c u12v2_x"
  u12v2X :: Word64 -> Word64

foreign import ccall unsafe "Runtime.c u12v2_y"
  u12v2Y :: Word64 -> Word64

-- Constants
-- ---------

tagT :: Tag -> TAG
tagT 0x00 = DP0
tagT 0x01 = DP1
tagT 0x02 = VAR
tagT 0x03 = APP
tagT 0x04 = ERA
tagT 0x05 = LAM
tagT 0x06 = SUP
tagT 0x07 = SUB
tagT 0x08 = REF
tagT 0x09 = CTR
tagT 0x0A = MAT
tagT tag  = error $ "unknown tag" ++ show tag

_DP0_, _DP1_, _VAR_, _APP_, _ERA_, _LAM_, _SUP_, _SUB_, _REF_, _CTR_, _MAT_ :: Tag
_DP0_ = 0x00
_DP1_ = 0x01
_VAR_ = 0x02
_APP_ = 0x03
_ERA_ = 0x04
_LAM_ = 0x05
_SUP_ = 0x06
_SUB_ = 0x07
_REF_ = 0x08
_CTR_ = 0x09
_MAT_ = 0x0A
