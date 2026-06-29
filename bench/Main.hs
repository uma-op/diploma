module Main(main) where

import Data.Char (isSpace)
import Data.List (isSuffixOf, sort)
import Refactoring.Parser (parseFormulaWithError)
import Refactoring.Prover.Benchmark
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import System.Environment (getArgs)
import System.Exit (ExitCode(ExitSuccess), die)
import System.FilePath ((</>), takeFileName)
import System.IO (hFlush, stdout)
import System.Posix.Process (exitImmediately)
import Text.Printf (printf)

main :: IO ()
main = do
  args <- getArgs
  root <- case args of
    [path] -> pure path
    _ -> die "Usage: diploma-bench <formula-file-or-directory>"

  inputs <- benchmarkInputs root
  putStrLn "name,result,clausification_ms,proving_ms,annotation_ms,total_ms"
  mapM_ runBenchmark inputs
  hFlush stdout
  exitImmediately ExitSuccess

benchmarkInputs :: FilePath -> IO [FilePath]
benchmarkInputs path = do
  isFile <- doesFileExist path
  isDir <- doesDirectoryExist path
  case (isFile, isDir) of
    (True, _) -> pure [path]
    (_, True) -> do
      entries <- sort <$> listDirectory path
      pure [path </> entry | entry <- entries, ".txt" `isSuffixOf` entry]
    _ -> die $ "Path does not exist: " ++ path

runBenchmark :: FilePath -> IO ()
runBenchmark path = do
  formulaText <- readFile path
  let formula = parseFormulaWithError $ trim formulaText
  result <- proveMeasured formula
  putStrLn $ csvLine (takeFileName path) result

csvLine :: FilePath -> BenchmarkResult -> String
csvLine name result =
  csvEscape name <> "," <>
  outcome <> "," <>
  formatMs (benchmarkClausificationMs result) <> "," <>
  formatMs (benchmarkProvingMs result) <> "," <>
  formatMs (benchmarkAnnotationMs result) <> "," <>
  formatMs (benchmarkTotalMs result)
  where
    outcome =
      case benchmarkOutcome result of
        BenchmarkValid -> "valid"
        BenchmarkInvalid -> "invalid"

formatMs :: Double -> String
formatMs = printf "%.3f"

csvEscape :: String -> String
csvEscape value =
  "\"" ++ concatMap escape value ++ "\""
  where
    escape '"' = "\"\""
    escape c = [c]

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace
  where
    dropWhileEnd predicate = reverse . dropWhile predicate . reverse
