-- //./Type.hs//
-- //./Show.hs//
-- //./Inject.hs//
-- //./Collapse.hs//

module HVML.Equal where

import Control.Monad (liftM2)
import HVML.Type
import HVML.Show

equal :: Core -> Core -> HVM Bool
equal a b = do
  -- putStrLn $ "eq " ++ coreToString a ++ "\n== " ++ coreToString b
  same a b

same (Var aNam) (Var bNam) = do
  return $ aNam == bNam
same (App aFun aArg) (App bFun bArg) = do
  eFun <- equal aFun bFun
  eArg <- equal aArg bArg
  return $ eFun && eArg
same (Lam aNam aBod) (Lam bNam bBod) = do
  equal aBod bBod
same Era Era = do
  return True
same (Sup aLab aA aB) (Sup bLab bA bB) = do
  error "unreachable"
same (Dup aLab aX aY aVal aBod) (Dup bLab bX bY bVal bBod) = do
  error "unreachable"
same (Typ aNam aBod) (Typ bNam bBod) = do
  error "unreachable"
same (Ann aVal aTyp) (Ann bVal bTyp) = do
  equal aVal bVal
same (Ctr aCid aArgs) (Ctr bCid bArgs)
  | aCid /= bCid = return False
  | length aArgs /= length bArgs = return False
  | otherwise = do
      results <- sequence $ zipWith equal aArgs bArgs
      return $ and results
same (Mat aVal aCses aAlts) (Mat bVal bCses bAlts)
  | length aCses /= length bCses || length aAlts /= length bAlts = return False
  | otherwise = do
      eVal <- equal aVal bVal
      eCses <- sequence [equal av bv | ((ak,av),(bk,bv)) <- zip aCses bCses, ak == bk]
      eAlts <- sequence [equal ab bb | ((ac,af,ab),(bc,bf,bb)) <- zip aAlts bAlts, ac == bc && af == bf]
      return $ eVal && and eCses && and eAlts
same (U32 aVal) (U32 bVal) = do
  return $ aVal == bVal
same (Chr aVal) (Chr bVal) = do
  return $ aVal == bVal
same (Op2 aOp aA aB) (Op2 bOp bA bB)
  | aOp /= bOp = return False
  | otherwise = liftM2 (&&) (equal aA bA) (equal aB bB)
same (Let aMod aNam aVal aBod) (Let bMod bNam bVal bBod)
  | aMod /= bMod = return False
  | otherwise = liftM2 (&&) (equal aVal bVal) (equal aBod bBod)
same _ _ = do
  return False

check :: Core -> HVM Bool
check (Var nam) = do
  return True
check (App fun arg) = do
  fun <- check fun
  arg <- check arg
  return $ fun && arg
check (Lam nam bod) = do
  bod <- check bod
  return bod
check Era = do
  return True
check (Sup lab a b) = do
  a <- check a
  b <- check b
  return $ a && b
check (Dup lab x y val bod) = do
  val <- check val
  bod <- check bod
  return $ val && bod
check (Typ nam bod) = do
  bod <- check bod
  return bod
check (Ann val typ) = case val of 
  Ann valVal valTyp -> do
    eql <- equal typ valTyp
    val <- check valVal
    return $ eql && val
  otherwise -> do
    return False
check (Ctr cid args) = do
  args <- mapM check args
  return $ and args
check (Mat val cses alts) = do
  val <- check val
  cses <- mapM (check . snd) cses
  alts <- mapM (\(_,_,bod) -> check bod) alts
  return $ val && and cses && and alts
check (U32 val) = do
  return True
check (Chr val) = do
  return True
check (Op2 op a b) = do
  a <- check a
  b <- check b
  return $ a && b
check (Let mod nam val bod) = do
  val <- check val
  bod <- check bod
  return $ val && bod
