-- //./Type.hs//

-- FIXME: when SUP labels have large vals, this takes a lot of time.

module HVML.Collapse where

import Control.Monad (ap, forM, forM_)
import Control.Monad.IO.Class
import Data.Char (chr, ord)
import Data.IORef
import Data.Word
import HVML.Show
import HVML.Type
import System.Exit (exitFailure)
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
bind k f = fork k IM.empty where
  -- fork :: Collapse a -> IntMap (Bin -> Bin) -> Collapse b
  fork CEra         paths = CEra
  fork (CVal v)     paths = pass (f v) (IM.map (\x -> x E) paths)
  fork (CSup k x y) paths =
    let lft = fork x $ IM.alter (\x -> Just (maybe id putO x)) (fromIntegral k) paths in
    let rgt = fork y $ IM.alter (\x -> Just (maybe id putI x)) (fromIntegral k) paths in
    CSup k lft rgt 

  -- pass :: Collapse b -> IntMap Bin -> Collapse b
  pass CEra         paths = CEra
  pass (CVal v)     paths = CVal v
  pass (CSup k x y) paths = case IM.lookup (fromIntegral k) paths of
    Just (O p) -> pass x (IM.insert (fromIntegral k) p paths)
    Just (I p) -> pass y (IM.insert (fromIntegral k) p paths)
    _          -> CSup k x y

  -- putO :: (Bin -> Bin) -> (Bin -> Bin)
  putO bs = \x -> bs (O x)

  -- putI :: (Bin -> Bin) -> (Bin -> Bin) 
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
    ERA -> do
      return Era

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

    TYP -> do
      let loc = termLoc term
      name <- genName namesRef (loc + 0)
      bod0 <- collapseDupsAt state reduceAt book (loc + 1)
      return $ Typ name bod0

    ANN -> do
      let loc = termLoc term
      val0 <- collapseDupsAt state reduceAt book (loc + 0)
      typ0 <- collapseDupsAt state reduceAt book (loc + 1)
      return $ Ann val0 typ0

    VAR -> do
      let loc = termLoc term
      sub <- got loc
      if termTag sub /= _SUB_
      then do
        error "Internal Error: VAR does not point to SUB"
      else do
        name <- genName namesRef loc
        return $ Var name

    DP0 -> do
      let loc = termLoc term
      let lab = termLab term
      sb0 <- got (loc+0)
      sb1 <- got (loc+1)
      if termTag sb1 /= _SUB_
      then do
        error "Internal Error: DP0 does not point to SUB"
      else do
        let newPaths = IM.alter (Just . maybe [0] (0:)) (fromIntegral lab) paths
        collapseDupsAt (newPaths, namesRef) reduceAt book (loc + 0)

    DP1 -> do
      let loc = termLoc term
      let lab = termLab term
      sb0 <- got (loc+0)
      sb1 <- got (loc+1)
      if termTag sb1 /= _SUB_
      then do
        error "Internal Error: DP1 does not point to SUB"
      else do
        let newPaths = IM.alter (Just . maybe [1] (1:)) (fromIntegral lab) paths
        collapseDupsAt (newPaths, namesRef) reduceAt book (loc + 0)

    CTR -> do
      let loc = termLoc term
      let lab = termLab term
      let cid = u12v2X lab
      let ari = u12v2Y lab
      let aux = if ari == 0 then [] else [loc + i | i <- [0..ari-1]]
      fds0 <- forM aux (collapseDupsAt state reduceAt book)
      return $ Ctr cid fds0

    MAT -> do
      let loc = termLoc term
      let len = termLab term
      let aux = if len == 0 then [] else [loc + 1 + i | i <- [0..len-1]]
      val0 <- collapseDupsAt state reduceAt book (loc + 0)
      css0 <- forM aux $ \h -> do
        bod <- collapseDupsAt state reduceAt book h
        return $ ("#", [], bod) -- TODO: recover constructor and fields
      return $ Mat val0 [] css0

    W32 -> do
      let val = termLoc term
      return $ U32 (fromIntegral val)

    CHR -> do
      let val = termLoc term
      return $ Chr (chr (fromIntegral val))

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

    tag -> do
      putStrLn ("unexpected-tag:" ++ show tag)
      exitFailure

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
  Dup lab x y val body -> do
    val <- collapseSups book val
    body <- collapseSups book body
    return $ Dup lab x y val body
  Typ nam bod -> do
    body <- collapseSups book bod
    return $ Typ nam body
  Ann val typ -> do
    val <- collapseSups book val
    typ <- collapseSups book typ
    return $ Ann val typ
  Ctr cid fields -> do
    fields <- mapM (collapseSups book) fields
    return $ Ctr cid fields
  Mat val mov css -> do
    val <- collapseSups book val
    mov <- mapM (\(key, expr) -> do
      expr <- collapseSups book expr
      return (key, expr)) mov
    css <- mapM (\(ctr, fds, bod) -> do
      bod <- collapseSups book bod
      return (ctr, fds, bod)) css
    return $ Mat val mov css
  U32 val -> do
    return $ U32 val
  Chr val -> do
    return $ Chr val
  Op2 op x y -> do
    x <- collapseSups book x
    y <- collapseSups book y
    return $ Op2 op x y
  Let mode name val body -> do
    val <- collapseSups book val
    body <- collapseSups book body
    return $ Let mode name val body
  Era -> do
    CEra
  Sup lab tm0 tm1 -> do
    let tm0' = collapseSups book tm0
    let tm1' = collapseSups book tm1
    CSup lab tm0' tm1'

-- Tree Collapser
-- --------------

doCollapseAt :: ReduceAt -> Book -> Loc -> HVM (Collapse Core)
doCollapseAt reduceAt book host = do
  namesRef <- newIORef MS.empty
  let state = (IM.empty, namesRef)
  core <- collapseDupsAt state reduceAt book host
  return $ collapseSups book core

-- Priority Queue
-- --------------

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

-- Flattener
-- ---------

flattenDFS :: Collapse a -> [a]
flattenDFS (CSup k a b) = flatten a ++ flatten b
flattenDFS (CVal x)     = [x]
flattenDFS CEra         = []

flattenPQ :: Collapse a -> [a]
flattenPQ term = go term (PQLeaf :: PQ (Collapse a)) where
  go (CSup k a b) pq = go CEra (pqPut (k,a) $ pqPut (k,b) $ pq)
  go (CVal x)     pq = x : go CEra pq
  go CEra         pq = case pqPop pq of
    Just ((k,v),pq) -> go v pq
    Nothing         -> []

flatten :: Collapse a -> [a]
flatten = flattenPQ

-- Flat Collapser
-- --------------

doCollapseFlatAt :: ReduceAt -> Book -> Loc -> HVM [Core]
doCollapseFlatAt reduceAt book host = do
  coll <- doCollapseAt reduceAt book host
  return $ flatten coll
