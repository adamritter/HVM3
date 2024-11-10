-- Type.hs:
-- //./Type.hs//

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Monad (when, forM_)
import Data.FileEmbed
import Foreign.C.Types
import Foreign.LibFFI
import Foreign.LibFFI.Types
import System.CPUTime
import System.Environment (getArgs)
import System.Exit (exitWith, ExitCode(ExitSuccess, ExitFailure))
import System.IO
import System.IO (readFile)
import System.Posix.DynamicLinker
import System.Process (callCommand)
import qualified Data.Map.Strict as MS

import HVML.Compile
import HVML.Extract
import HVML.Inject
import HVML.Parse
import HVML.Reduce
import HVML.Show
import HVML.Type

runtime_c :: String
runtime_c = $(embedStringFile "./src/HVML/Runtime.c")

-- Main
-- ----

main :: IO ()
main = do
  args <- getArgs
  result <- case args of
    ["run", file, "-s"]   -> cliRun file False True
    ["run", file]         -> cliRun file False False
    ["run-c", file, "-s"] -> cliRun file True True
    ["run-c", file]       -> cliRun file True False
    ["help"]              -> printHelp
    _                     -> printHelp
  case result of
    Left err -> do
      putStrLn err
      exitWith (ExitFailure 1)
    Right _ -> do
      exitWith ExitSuccess

-- CLI Commands
-- ------------

cliRun :: FilePath -> Bool -> Bool -> IO (Either String ())
cliRun filePath compiled showStats = do
  -- Initialize the HVM
  hvmInit

  -- TASK: instead of parsing a core term out of the file, lets parse a Book.
  code <- readFile filePath
  book <- doParseBook code

  -- Create the C file content
  let funcs = map (\ (fid, core) -> compile book fid core) (MS.toList (idToCore book))
  let bookC = unlines $ [runtime_c] ++ funcs

  -- Compile to native
  when compiled $ do
    -- Write the C file
    writeFile "./.hvm_book.c" bookC
    
    -- Compile to shared library
    callCommand "gcc -O2 -fPIC -shared .hvm_book.c -o .hvm_book.so"
    
    -- Load the dynamic library
    bookLib <- dlopen "./.hvm_book.so" [RTLD_NOW]

    -- Remove both generated files
    callCommand "rm .hvm_book.c .hvm_book.so"

    -- Link compiled state
    hvmGotState <- hvmGetState
    hvmSetState <- dlsym bookLib "hvm_set_state"
    callFFI hvmSetState retVoid [argPtr hvmGotState]
    
    -- Register compiled functions
    forM_ (MS.keys (idToCore book)) $ \ fid -> do
      funPtr <- dlsym bookLib ("F_" ++ show fid)
      hvmDefine fid funPtr

  -- Abort when main isn't present
  when (not $ MS.member "main" (nameToId book)) $ do
    putStrLn "Error: 'main' not found."
    exitWith (ExitFailure 1)

  -- Normalize main
  init <- getCPUTime
  root <- doInjectCore book (Ref "main" $ nameToId book MS.! "main")
  -- norm <- doExtractCore root
  done <- (if compiled then normalC else normal) book root
  norm <- doExtractCore done
  putStrLn $ coreToString norm

  -- Show stats
  when showStats $ do
    end <- getCPUTime
    itr <- getItr
    len <- getLen
    let diff = fromIntegral (end - init) / (10^9) :: Double
    let mips = (fromIntegral itr / 1000000.0) / (diff / 1000.0)
    putStrLn $ "ITRS: " ++ show itr
    putStrLn $ "TIME: " ++ show diff ++ "ms"
    putStrLn $ "SIZE: " ++ show len
    putStrLn $ "MIPS: " ++ show mips
    return ()

  -- Finalize
  hvmFree
  return $ Right ()

printHelp :: IO (Either String ())
printHelp = do
  putStrLn "HVM-Lazy usage:"
  putStrLn "  hvml run [-s] <file>  # Normalizes the specified file"
  putStrLn "  hvml help             # Shows this help message"
  return $ Right ()
