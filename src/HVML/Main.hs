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
import Text.Printf
import qualified Data.Map.Strict as MS

import HVML.Collapse
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

data RunMode
  = Normalize
  | Collapse
  | Search
  deriving Eq

main :: IO ()
main = do
  args <- getArgs
  result <- case args of
    ("run" : file : args) -> do
      let compiled  = "-c" `elem` args
      let collapse  = "-C" `elem` args
      let search    = "-S" `elem` args
      let showStats = "-s" `elem` args
      let mode = if collapse then Collapse else if search then Search else Normalize
      cliRun file compiled mode showStats
    ["help"] -> printHelp
    _ -> printHelp
  case result of
    Left err -> do
      putStrLn err
      exitWith (ExitFailure 1)
    Right _ -> do
      exitWith ExitSuccess

printHelp :: IO (Either String ())
printHelp = do
  putStrLn "HVM-Lazy usage:"
  putStrLn "  hvml help # Shows this help message"
  putStrLn "  hvml run <file> [-c] [-C] [-s] # Normalizes the file's main"
  putStrLn "    -c # Runs with compiled mode (fast)"
  putStrLn "    -C # Collapse the result to a list of λ-Terms"
  putStrLn "    -S # Search (collapse, then print the 1st λ-Term)"
  putStrLn "    -s # Show statistics"
  return $ Right ()

-- CLI Commands
-- ------------

cliRun :: FilePath -> Bool -> RunMode -> Bool -> IO (Either String ())
cliRun filePath compiled mode showStats = do
  -- Initialize the HVM
  hvmInit

  -- TASK: instead of parsing a core term out of the file, lets parse a Book.
  code <- readFile filePath
  book <- doParseBook code

  -- Create the C file content
  let funcs = map (\ (fid, _) -> compile book fid) (MS.toList (idToFunc book))
  let mainC = unlines $ [runtime_c] ++ funcs ++ [genMain book]

  -- Compile to native
  when compiled $ do
    -- Write the C file
    writeFile "./.main.c" mainC
    
    -- Compile to shared library
    callCommand "gcc -O2 -fPIC -shared .main.c -o .main.so"
    
    -- Load the dynamic library
    bookLib <- dlopen "./.main.so" [RTLD_NOW]

    -- Remove both generated files
    callCommand "rm .main.so"
    
    -- Register compiled functions
    forM_ (MS.keys (idToFunc book)) $ \ fid -> do
      funPtr <- dlsym bookLib (idToName book MS.! fid ++ "_f")
      hvmDefine fid funPtr

    -- Link compiled state
    hvmGotState <- hvmGetState
    hvmSetState <- dlsym bookLib "hvm_set_state"
    callFFI hvmSetState retVoid [argPtr hvmGotState]

  -- Abort when main isn't present
  when (not $ MS.member "main" (nameToId book)) $ do
    putStrLn "Error: 'main' not found."
    exitWith (ExitFailure 1)

  -- Normalize main
  init <- getCPUTime
  root <- doInjectCoreAt book (Ref "main" (nameToId book MS.! "main") []) 0 []
  rxAt <- if compiled
    then return reduceCAt
    else return reduceAt
  vals <- if mode == Collapse || mode == Search
    then doCollapseAt rxAt book 0
    else do
      core <- doExtractCoreAt rxAt book 0
      return [(doLiftDups core)]

  -- Print all collapsed results
  when (mode == Collapse) $ do
    forM_ vals $ \ term ->
      putStrLn $ coreToString term

  -- Prints just the first collapsed result
  when (mode == Search || mode == Normalize) $ do
    putStrLn $ coreToString (head vals)

  -- Prints total time
  end <- getCPUTime

  -- Show stats
  when showStats $ do
    itrs <- getItr
    size <- getLen
    let time = fromIntegral (end - init) / (10^12) :: Double
    let mips = (fromIntegral itrs / 1000000.0) / time
    printf "WORK: %llu interactions\n" itrs
    printf "TIME: %.7f seconds\n" time
    printf "SIZE: %llu nodes\n" size
    printf "PERF: %.3f MIPS\n" mips
    return ()

  -- Finalize
  hvmFree
  return $ Right ()

genMain :: Book -> String
genMain book =
  let mainFid = nameToId book MS.! "main"
      registerFuncs = unlines ["  hvm_define(" ++ show fid ++ ", " ++ idToName book MS.! fid ++ "_f);" | fid <- MS.keys (idToFunc book)]
  in unlines
    [ "int main() {"
    , "  hvm_init();"
    , registerFuncs
    , "  clock_t start = clock();"
    , "  Term root = term_new(REF, u12v2_new("++show mainFid++",0), 0);"
    , "  normal(root);"
    , "  double time = (double)(clock() - start) / CLOCKS_PER_SEC * 1000;"
    , "  printf(\"WORK: %llu interactions\\n\", get_itr());"
    , "  printf(\"TIME: %.3fs seconds\\n\", time / 1000.0);"
    , "  printf(\"SIZE: %u nodes\\n\", get_len());"
    , "  printf(\"PERF: %.3f MIPS\\n\", (get_itr() / 1000000.0) / (time / 1000.0));"
    , "  hvm_free();"
    , "  return 0;"
    , "}"
    ]
