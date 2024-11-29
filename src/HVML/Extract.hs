-- //./Type.hs//
-- //./Inject.hs//

module HVML.Extract where

import Control.Monad (foldM)
import Control.Monad.State
import Data.Char (chr, ord)
import Data.IORef
import Data.Word
import HVML.Show
import HVML.Type
import System.IO.Unsafe (unsafeInterleaveIO)
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as MS

import Debug.Trace

type ExtractState = (IORef IS.IntSet, IORef (MS.Map Loc String))

genName :: ExtractState -> Loc -> HVM String
genName (_, namsRef) loc = do
  nams <- readIORef namsRef
  case MS.lookup loc nams of
    Just name -> return name
    Nothing -> do
      let newName = genNameFromIndex (MS.size nams)
      modifyIORef' namsRef (MS.insert loc newName)
      return newName

genNameFromIndex :: Int -> String
genNameFromIndex n = go (n + 1) "" where
  go n ac | n == 0    = ac
          | otherwise = go q (chr (ord 'a' + r) : ac)
          where (q,r) = quotRem (n - 1) 26

extractCoreAt :: ExtractState -> ReduceAt -> Book -> Loc -> HVM Core
extractCoreAt state@(dupsRef, _) reduceAt book host = unsafeInterleaveIO $ do
  term <- reduceAt book host
  case tagT (termTag term) of
    ERA -> do
      return Era

    LET -> do
      let loc  = termLoc term
      let mode = modeT (termLab term)
      name <- genName state (loc + 0)
      val  <- extractCoreAt state reduceAt book (loc + 1)
      bod  <- extractCoreAt state reduceAt book (loc + 2)
      return $ Let mode name val bod

    LAM -> do
      let loc = termLoc term
      name <- genName state (loc + 0)
      bod  <- extractCoreAt state reduceAt book (loc + 1)
      return $ Lam name bod
    
    APP -> do
      let loc = termLoc term
      fun <- extractCoreAt state reduceAt book (loc + 0)
      arg <- extractCoreAt state reduceAt book (loc + 1)
      return $ App fun arg
    
    SUP -> do
      let loc = termLoc term
      let lab = termLab term
      tm0 <- extractCoreAt state reduceAt book (loc + 0)
      tm1 <- extractCoreAt state reduceAt book (loc + 1)
      return $ Sup lab tm0 tm1

    TYP -> do
      let loc = termLoc term
      name <- genName state (loc + 0)
      bod  <- extractCoreAt state reduceAt book (loc + 1)
      return $ Typ name bod
    
    ANN -> do
      let loc = termLoc term
      val <- extractCoreAt state reduceAt book (loc + 0)
      typ <- extractCoreAt state reduceAt book (loc + 1)
      return $ Ann val typ
    
    VAR -> do
      let loc = termLoc term
      sub <- got (loc + 0)
      if termTag sub == _SUB_
        then do
          name <- genName state loc
          return $ Var name
        else do
          extractCoreAt state reduceAt book (loc + 0)

    DP0 -> do
      let loc = termLoc term
      let lab = termLab term
      dups <- readIORef dupsRef
      if IS.member (fromIntegral loc) dups
      then do
        name <- genName state (loc + 0)
        return $ Var name
      else do
        dp0 <- genName state (loc + 0)
        dp1 <- genName state (loc + 1)
        val <- extractCoreAt state reduceAt book loc
        modifyIORef' dupsRef (IS.insert (fromIntegral loc))
        return $ Dup lab dp0 dp1 val (Var dp0)
    
    DP1 -> do
      let loc = termLoc term
      let lab = termLab term
      dups <- readIORef dupsRef
      if IS.member (fromIntegral loc) dups
      then do
        name <- genName state (loc + 1)
        return $ Var name
      else do
        dp0 <- genName state (loc + 0)
        dp1 <- genName state (loc + 1)
        val <- extractCoreAt state reduceAt book loc
        modifyIORef' dupsRef (IS.insert (fromIntegral loc))
        return $ Dup lab dp0 dp1 val (Var dp1)

    CTR -> do
      let loc = termLoc term
      let lab = termLab term
      let cid = u12v2X lab
      let ari = u12v2Y lab
      let ars = if ari == 0 then [] else [0..ari-1]
      fds <- mapM (\i -> extractCoreAt state reduceAt book (loc + i)) ars
      return $ Ctr cid fds
    
    MAT -> do
      let loc = termLoc term
      let len = termLab term
      val <- extractCoreAt state reduceAt book (loc + 0)
      css <- mapM (\i -> extractCoreAt state reduceAt book (loc + 1 + i)) [0..len-1]
      css <- mapM (\c -> return ("#", [], c)) css -- FIXME: recover names and fields on extraction (must store id)
      return $ Mat val [] css
    
    W32 -> do
      let val = termLoc term
      return $ U32 (fromIntegral val)

    CHR -> do
      let val = termLoc term
      return $ Chr (chr (fromIntegral val))
    
    OPX -> do
      let loc = termLoc term
      let opr = toEnum (fromIntegral (termLab term))
      nm0 <- extractCoreAt state reduceAt book (loc + 0)
      nm1 <- extractCoreAt state reduceAt book (loc + 1)
      return $ Op2 opr nm0 nm1
    
    OPY -> do
      let loc = termLoc term
      let opr = toEnum (fromIntegral (termLab term))
      nm0 <- extractCoreAt state reduceAt book (loc + 0)
      nm1 <- extractCoreAt state reduceAt book (loc + 1)
      return $ Op2 opr nm0 nm1
    
    REF -> do
      let loc = termLoc term
      let lab = termLab term
      let fid = u12v2X lab
      let ari = u12v2Y lab
      let aux = if ari == 0 then [] else [0..ari-1]
      arg <- mapM (\i -> extractCoreAt state reduceAt book (loc + i)) aux
      let name = MS.findWithDefault "?" fid (idToName book)
      return $ Ref name fid arg
    
    _ -> do
      return Era

doExtractCoreAt :: ReduceAt -> Book -> Loc -> HVM Core
doExtractCoreAt reduceAt book loc = do
  dupsRef <- newIORef IS.empty
  namsRef <- newIORef MS.empty
  let state = (dupsRef, namsRef)
  core <- extractCoreAt state reduceAt book loc
  return core
  -- return $ doLiftDups core

-- Lifting Dups
-- ------------

liftDups :: Core -> State (Core -> Core) Core
liftDups (Var nam) = return $ Var nam
liftDups (Ref nam fid arg) = do
  arg <- mapM liftDups arg
  return $ Ref nam fid arg
liftDups Era = return Era
liftDups (Lam str bod) = do
  bod <- liftDups bod
  return $ Lam str bod
liftDups (App fun arg) = do
  fun <- liftDups fun
  arg <- liftDups arg
  return $ App fun arg
liftDups (Sup lab tm0 tm1) = do
  tm0 <- liftDups tm0
  tm1 <- liftDups tm1
  return $ Sup lab tm0 tm1
liftDups (Dup lab dp0 dp1 val bod) = do
  val <- liftDups val
  bod <- liftDups bod
  modify (\oldState k -> oldState (Dup lab dp0 dp1 val k))
  return bod
liftDups (Typ nam bod) = do
  bod <- liftDups bod
  return $ Typ nam bod
liftDups (Ann val typ) = do
  val <- liftDups val
  typ <- liftDups typ
  return $ Ann val typ
liftDups (Ctr cid fds) = do
  fds <- mapM liftDups fds
  return $ Ctr cid fds
liftDups (Mat val mov css) = do
  val <- liftDups val
  mov <- mapM (\(key, val) -> do
    val <- liftDups val
    return (key, val)) mov
  css <- mapM (\(ctr, fds, bod) -> do
    bod <- liftDups bod
    return (ctr, fds, bod)) css
  return $ Mat val mov css
liftDups (U32 val) = do
  return $ U32 val
liftDups (Chr val) = do
  return $ Chr val
liftDups (Op2 opr nm0 nm1) = do
  nm0 <- liftDups nm0
  nm1 <- liftDups nm1
  return $ Op2 opr nm0 nm1
liftDups (Let mod nam val bod) = do
  val <- liftDups val
  bod <- liftDups bod
  return $ Let mod nam val bod

doLiftDups :: Core -> Core
doLiftDups term =
  let (liftedTerm, finalState) = runState (liftDups term) id
  in finalState liftedTerm
