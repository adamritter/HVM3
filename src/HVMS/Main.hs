module Main where

import Control.Monad (when)
import System.CPUTime
import System.Environment (getArgs)
import System.Exit (exitWith, ExitCode(ExitSuccess, ExitFailure))
import System.IO (readFile)

import HVMS.Type
import HVMS.Inject
import HVMS.Extract
import HVMS.Parse
import HVMS.Show
import HVMS.Normal

-- Main
-- ----

main :: IO ()
main = do
  args <- getArgs
  result <- case args of
    ["run", file, "-s"] -> cliRun file True
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
  let net = doParseNet code
  root <- doInjectNet net
  norm <- normal root
  set 0 norm
  norm' <- doExtractNet norm []
  putStrLn $ netToString norm'

  when showStats $ do
    end <- getCPUTime
    let diff = fromIntegral (end - start) / (10^9) :: Double
    itr <- incItr
    let len  = 0 -- RNOD_END -- TODO: expose this via FFI
    let mips = (fromIntegral itr / 1000000.0) / (diff / 1000.0)
    putStrLn $ "ITRS: " ++ show itr
    putStrLn $ "TIME: " ++ show diff ++ "ms"
    putStrLn $ "SIZE: " ++ show len
    putStrLn $ "MIPS: " ++ show mips

  hvmFree
  return $ Right ()

printHelp :: IO (Either String ())
printHelp = do
  putStrLn "HVM-Strict usage:"
  putStrLn "  hvms run [-s] <file>  # Normalizes the specified file"
  putStrLn "  hvms help             # Shows this help message"
  return $ Right ()
