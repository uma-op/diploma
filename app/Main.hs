module Main(main) where

import Data.Maybe
import Control.Monad.State
import Data.Functor
import Z3.Base
import Data.Bifunctor
import Data.Char (isSpace)
import qualified Data.Map as Map
import qualified Data.List as List
import System.Environment (getArgs)
import System.Exit (die)

import qualified ProverR
import qualified World
import Proof
import Term

import IncrementalSolver(IncrementalSolver(..))
import qualified IncrementalSolver

import qualified CounterModel
import qualified ProofDot
import Parser (parseFormula, parseFormulaWithError)
import Sequent
import Clause
import Formula
import ClassicSeqProver

main :: IO ()
main = test2

trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

test2 :: IO ()
test2 = do
  args <- getArgs
  formulaFile <- case args of
    [path] -> pure path
    _ -> die "Usage: diploma-exe <formula-file>"
  formulaText <- readFile formulaFile
  let formula = parseFormulaWithError $ trim formulaText

  IncrementalSolver context solver <- IncrementalSolver.newSolver
  result <- ProverR.proveR context solver formula
  case result of
    ProverR.Invalid counterModel -> do
      putStrLn . ("Result model:\n" ++) =<< CounterModel.counterModelToString context counterModel
      putStrLn =<< CounterModel.counterModelToDot context counterModel
    ProverR.Valid (plaindt, clausificationHistory) -> do 
      putStrLn "Valid"
      let carrowRules = map (\(_, _, rule) -> rule) plaindt
      let clausificationRules = map snd clausificationHistory
      let carrowNodes = map (\(x, y, z) -> CArrowNode z y x) plaindt
      let (annotatedCArrowNodes, st) = runState (annotateCArrowNodes carrowNodes) newEnvironment

      putStrLn "CARROW:"
      putStrLn $ List.intercalate "\n-------\n" $ map (\(iseq, cseq) -> show cseq ++ "\n%\n" ++ sequentToString iseq) annotatedCArrowNodes
      mapM_ (\(i, ljt) -> putStrLn $ ProofDot.ljtToDot i ljt) (zip [0 ..] (map snd annotatedCArrowNodes))

      let lastCArrowSeq = fst $ last annotatedCArrowNodes

      let clausificationNodes = map (\(x, y) -> ClausificationNode y x) clausificationHistory 
      let (annotatedClausificationNodes, _) = runState (annotateClausificationNodes lastCArrowSeq clausificationNodes) st

      putStrLn "CLAUSIFICATION:"
      putStrLn $ List.intercalate "\n-------\n" $ map sequentToString annotatedClausificationNodes
      putStrLn $ ProofDot.cArrowClausificationToDot carrowRules annotatedCArrowNodes clausificationRules annotatedClausificationNodes

      let lastSeq = last annotatedClausificationNodes

      putStrLn $ sequentToString lastSeq

-- test :: IO ()
-- test = do
--   let s = ClassicPlainSequent
--         [
--           FlatClauseFormula [Variable "a"] [Variable "b"] (Implication [variable "a", variable "b"]),
--           FlatClauseFormula [Variable "b"] [Variable "g"] (Implication [variable "b", variable "g"]),
--           FlatClauseFormula [Variable "b"] [Variable "b"] (Implication [variable "b", variable "b"])
--         ]
--         [
--           Variable "a"
--         ]
--         (Variable "b") 
-- 
--   let classicDT = proveLJT s
--   print classicDT
-- 
--   let (annotated, _) = runState (annotateLJTNode classicDT) newEnvironment
--   putStrLn (sequentToString annotated)
-- 
--   return undefined
-- 


--foo = \_32 -> _32 (const $ Right (\_44 -> _32 (\_57 -> Left (\_72 -> (_57 _72)))))

