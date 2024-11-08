module Main where

import Control.Monad (when)
import System.CPUTime
import System.Environment (getArgs)
import System.Exit (exitWith, ExitCode(ExitSuccess, ExitFailure))
import System.IO (readFile)

import HVML.Type
import HVML.Inject
import HVML.Extract
import HVML.Parse
import HVML.Show
import HVML.Normal

-- Main
-- ----

main :: IO ()
main = do
  args <- getArgs
  result <- case args of
    ["run", file, "-s"] -> cliRun file True
    ["run", "-s", file] -> cliRun file True
    ["run", file]       -> cliRun file False
    ["help"]            -> printHelp
    _                   -> printHelp
  case result of
    Left err -> do
      putStrLn err
      exitWith (ExitFailure 1)
    Right _ -> do
      exitWith ExitSuccess

-- CLI Commands
-- ------------

cliRun :: FilePath -> Bool -> IO (Either String ())
cliRun filePath showStats = do
  start <- getCPUTime
  hvmInit

  code <- readFile filePath
  let term = doParseCore code
  root <- doInjectCore term
  norm <- normal root
  set 0 norm
  norm' <- doExtractCore norm
  putStrLn $ coreToString norm'

  when showStats $ do
    end <- getCPUTime
    let diff = fromIntegral (end - start) / (10^9) :: Double
    itr <- getItr
    len <- getLen
    let mips = (fromIntegral itr / 1000000.0) / (diff / 1000.0)
    putStrLn $ "ITRS: " ++ show itr
    putStrLn $ "TIME: " ++ show diff ++ "ms"
    putStrLn $ "SIZE: " ++ show len
    putStrLn $ "MIPS: " ++ show mips

  hvmFree
  return $ Right ()

printHelp :: IO (Either String ())
printHelp = do
  putStrLn "HVM usage:"
  putStrLn "  hvm run [-s] <file>  # Normalizes the specified file"
  putStrLn "  hvm help             # Shows this help message"
  return $ Right ()