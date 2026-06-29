module Main(main) where

import Refactoring.Prover.Prover (prove)
import Refactoring.Parser (parseFormulaWithError)
import System.Environment (getArgs)
import System.Exit (die)
import Data.Char (isSpace)

main :: IO ()
main = do
  args <- getArgs
  formulaFile <- case args of
    [path] -> pure path
    _ -> die "Usage: diploma-exe <formula-file>"

  formulaText <- readFile formulaFile
  let formula = parseFormulaWithError $ trim formulaText

  prove formula

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace
  where
    dropWhileEnd predicate = reverse . dropWhile predicate . reverse
