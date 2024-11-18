-- //./Type.hs//

module HVML.Collapse where

import Control.Monad (ap, forM_)
import Control.Monad.IO.Class
import Data.Char (chr, ord)
import Data.IORef
import Data.Word
import HVML.Type
import HVML.Show
import System.IO.Unsafe (unsafeInterleaveIO)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as MS

-- The Collapse Monad
-- ------------------
-- See: https://gist.github.com/VictorTaelin/60d3bc72fb4edefecd42095e44138b41

-- A bit-string
data Bin
  = O Bin
  | I Bin
  | E
  deriving Show

-- A Collapse is a tree of superposed values
data Collapse a = CSup Word64 (Collapse a) (Collapse a) | CVal a | CEra
  deriving Show

-- The Collapse Monad
bind :: Collapse a -> (a -> Collapse b) -> Collapse b
bind a f = fork a (repeat (\x -> x)) where
  fork CEra         paths = CEra
  fork (CVal v)     paths = pass (f v) (map (\x -> x E) paths)
  fork (CSup k x y) paths = CSup k (fork x (mut k putO paths)) (fork y (mut k putI paths))
  pass CEra         paths = CEra
  pass (CVal v)     paths = CVal v
  pass (CSup k x y) paths = case paths !! fromIntegral k of
    E   -> CSup k x y
    O p -> pass x (mut k (\_->p) paths)
    I p -> pass y (mut k (\_->p) paths)
  putO bs = \x -> bs (O x)
  putI bs = \x -> bs (I x)

-- Mutates an element at given index in a list
mut :: Word64 -> (a -> a) -> [a] -> [a]
mut 0 f (x:xs) = f x : xs
mut n f (x:xs) = x : mut (n-1) f xs
mut _ _ []     = []

instance Functor Collapse where
  fmap f (CVal v)     = CVal (f v)
  fmap f (CSup k x y) = CSup k (fmap f x) (fmap f y)
  fmap _ CEra         = CEra

instance Applicative Collapse where
  pure  = CVal
  (<*>) = ap

instance Monad Collapse where
  return = pure
  (>>=)  = bind

-- Dup Collapser
-- -------------

type CollapseDupsState = (IM.IntMap [Int], IORef (MS.Map Loc String))

collapseDupsAt :: CollapseDupsState -> ReduceAt -> Book -> Loc -> HVM Core
collapseDupsAt state@(paths, namesRef) reduceAt book host = unsafeInterleaveIO $ do
  term <- reduceAt book host
  case tagT (termTag term) of
    ERA -> return Era

    LET -> do
      let loc = termLoc term
      let mode = modeT (termLab term)
      name <- genName namesRef (loc + 0)
      val0 <- collapseDupsAt state reduceAt book (loc + 1)
      bod0 <- collapseDupsAt state reduceAt book (loc + 2)
      return $ Let mode name val0 bod0

    LAM -> do
      let loc = termLoc term
      name <- genName namesRef (loc + 0)
      bod0 <- collapseDupsAt state reduceAt book (loc + 1)
      return $ Lam name bod0

    APP -> do
      let loc = termLoc term
      fun0 <- collapseDupsAt state reduceAt book (loc + 0)
      arg0 <- collapseDupsAt state reduceAt book (loc + 1)
      return $ App fun0 arg0

    SUP -> do
      let loc = termLoc term
      let lab = termLab term
      case IM.lookup (fromIntegral lab) paths of
        Just (p:ps) -> do
          let newPaths = IM.insert (fromIntegral lab) ps paths
          collapseDupsAt (newPaths, namesRef) reduceAt book (loc + fromIntegral p)
        _ -> do
          tm00 <- collapseDupsAt state reduceAt book (loc + 0)
          tm11 <- collapseDupsAt state reduceAt book (loc + 1)
          return $ Sup lab tm00 tm11

    VAR -> do
      let key = termKey term
      sub <- got key
      if termTag sub /= _SUB_
      then do
        error "Internal Error: VAR does not point to SUB"
      else do
        name <- genName namesRef key
        return $ Var name

    DP0 -> do
      let loc = termLoc term
      let lab = termLab term
      let key = termKey term
      sub <- got key
      if termTag sub /= _SUB_
      then do
        error "Internal Error: DP0 does not point to SUB"
      else do
        let newPaths = IM.alter (Just . maybe [0] (0:)) (fromIntegral lab) paths
        collapseDupsAt (newPaths, namesRef) reduceAt book (loc + 2)

    DP1 -> do
      let loc = termLoc term
      let lab = termLab term
      let key = termKey term
      sub <- got key
      if termTag sub /= _SUB_
      then do
        error "Internal Error: DP1 does not point to SUB"
      else do
        let newPaths = IM.alter (Just . maybe [1] (1:)) (fromIntegral lab) paths
        collapseDupsAt (newPaths, namesRef) reduceAt book (loc + 2)

    CTR -> do
      let loc = termLoc term
      let lab = termLab term
      let cid = u12v2X lab
      let ari = u12v2Y lab
      fds0 <- mapM (collapseDupsAt state reduceAt book) [loc + i | i <- [0..ari-1]]
      return $ Ctr cid fds0

    MAT -> do
      let loc = termLoc term
      let len = termLab term
      val0 <- collapseDupsAt state reduceAt book (loc + 0)
      css0 <- mapM (collapseDupsAt state reduceAt book) [loc + 1 + i | i <- [0..len-1]]
      css1 <- mapM (\ cs -> return (0, cs)) css0
      return $ Mat val0 css1

    W32 -> do
      let val = termLoc term
      return $ U32 (fromIntegral val)

    OPX -> do
      let loc = termLoc term
      let opr = toEnum (fromIntegral (termLab term))
      nm00 <- collapseDupsAt state reduceAt book (loc + 0)
      nm10 <- collapseDupsAt state reduceAt book (loc + 1)
      return $ Op2 opr nm00 nm10

    OPY -> do
      let loc = termLoc term
      let opr = toEnum (fromIntegral (termLab term))
      nm00 <- collapseDupsAt state reduceAt book (loc + 0)
      nm10 <- collapseDupsAt state reduceAt book (loc + 1)
      return $ Op2 opr nm00 nm10

    REF -> do
      let loc = termLoc term
      let lab = termLab term
      let fid = u12v2X lab
      let ari = u12v2Y lab
      arg0 <- mapM (collapseDupsAt state reduceAt book) [loc + i | i <- [0..ari-1]]
      let name = MS.findWithDefault "?" fid (idToName book)
      return $ Ref name fid arg0

genName :: IORef (MS.Map Loc String) -> Loc -> HVM String
genName namesRef loc = do
  nameMap <- readIORef namesRef
  case MS.lookup loc nameMap of
    Just name -> return name
    Nothing -> do
      let newName = genNameFromIndex (MS.size nameMap)
      modifyIORef' namesRef (MS.insert loc newName)
      return newName

genNameFromIndex :: Int -> String
genNameFromIndex n = go (n + 1) "" where
  go n ac | n == 0    = ac
          | otherwise = go q (chr (ord 'a' + r) : ac)
          where (q,r) = quotRem (n - 1) 26

-- Sup Collapser
-- -------------

collapseSups :: Book -> Core -> Collapse Core
collapseSups book core = case core of
  Era -> return Era
  Var name -> return $ Var name
  Ref name fid args -> do
    args <- mapM (collapseSups book) args
    return $ Ref name fid args
  Lam name body -> do
    body <- collapseSups book body
    return $ Lam name body
  App fun arg -> do
    fun <- collapseSups book fun
    arg <- collapseSups book arg
    return $ App fun arg
  Sup lab tm0 tm1 -> do
    let tm0' = collapseSups book tm0
    let tm1' = collapseSups book tm1
    CSup lab tm0' tm1'
  Dup lab x y val body -> do
    val <- collapseSups book val
    body <- collapseSups book body
    return $ Dup lab x y val body
  Ctr cid fields -> do
    fields <- mapM (collapseSups book) fields
    return $ Ctr cid fields
  Mat val cases -> do
    val <- collapseSups book val
    cases <- mapM (\ (arity, expr) -> do
      expr <- collapseSups book expr
      return (arity, expr)) cases
    return $ Mat val cases
  U32 val -> return $ U32 val
  Op2 op x y -> do
    x <- collapseSups book x
    y <- collapseSups book y
    return $ Op2 op x y
  Let mode name val body -> do
    val <- collapseSups book val
    body <- collapseSups book body
    return $ Let mode name val body

-- Flattener
-- ---------

data PQ a
  = PQLeaf
  | PQNode (Word64, a) (PQ a) (PQ a)
  deriving (Show)

pqUnion :: PQ a -> PQ a -> PQ a
pqUnion PQLeaf heap = heap
pqUnion heap PQLeaf = heap
pqUnion heap1@(PQNode (k1,v1) l1 r1) heap2@(PQNode (k2,v2) l2 r2)
  | k1 <= k2  = PQNode (k1,v1) (pqUnion heap2 r1) l1
  | otherwise = PQNode (k2,v2) (pqUnion heap1 r2) l2

pqPop :: PQ a -> Maybe ((Word64, a), PQ a)
pqPop PQLeaf         = Nothing
pqPop (PQNode x l r) = Just (x, pqUnion l r)

pqPut :: (Word64,a) -> PQ a -> PQ a
pqPut (k,v) = pqUnion (PQNode (k,v) PQLeaf PQLeaf)

flatten :: Collapse a -> [a]
flatten term = go term (PQLeaf :: PQ (Collapse a)) where
  go (CSup k a b) pq = go CEra (pqPut (k,a) $ pqPut (k,b) $ pq)
  go (CVal x)     pq = x : go CEra pq
  go CEra         pq = case pqPop pq of
    Just ((k,v),pq) -> go v pq
    Nothing         -> []

-- Core Collapser
-- --------------

doCollapseAt :: ReduceAt -> Book -> Loc -> HVM [Core]
doCollapseAt reduceAt book host = do
  namesRef <- newIORef MS.empty
  let state = (IM.empty, namesRef)
  core <- collapseDupsAt state reduceAt book host
  return $ flatten (collapseSups book core)
