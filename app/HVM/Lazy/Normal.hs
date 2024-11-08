module HVM.Lazy.Normal where

import HVM.Lazy.Type

normal :: Term -> HVM Term
normal term = do
  wnf <- reduce term
  let tag = termTag wnf
      lab = termLab wnf
      loc = termLoc wnf
  case tagT tag of
    APP -> do
      fun <- got (loc + 0)
      arg <- got (loc + 1)
      fun <- normal fun
      arg <- normal arg
      set (loc + 0) fun
      set (loc + 1) arg
      return wnf
    LAM -> do
      bod <- got (loc + 1)
      bod <- normal bod
      set (loc + 1) bod
      return wnf
    SUP -> do
      tm0 <- got (loc + 0)
      tm1 <- got (loc + 1)
      tm0 <- normal tm0
      tm1 <- normal tm1
      set (loc + 0) tm0
      set (loc + 1) tm1
      return wnf
    DP0 -> do
      val <- got (loc + 2)
      val <- normal val
      set (loc + 2) val
      return wnf
    DP1 -> do
      val <- got (loc + 2)
      val <- normal val
      set (loc + 2) val
      return wnf
    _ -> return wnf
