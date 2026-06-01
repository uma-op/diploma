module Main(main) where

import Data.Maybe
import Control.Monad.State
import Data.Functor
import Z3.Base
import Data.Bifunctor
import qualified Data.Map as Map
import qualified Data.List as List

import qualified ProverR
import qualified World
import Proof
import Term

import IncrementalSolver(IncrementalSolver(..))
import qualified IncrementalSolver

import qualified CounterModel
import Parser (parseFormula, parseFormulaWithError)
import Sequent
import Clause
import Formula
import ClassicSeqProver

main :: IO ()
main = do
  test2

test2 :: IO ()
test2 = do
  -- let formula = Formula.disjunction (Formula.variable "a") (Formula.negation $ Formula.variable "a")
  -- let formula = Formula.disjunction
  --                 (Formula.implication (Formula.variable "a") (Formula.variable "b"))
  --                 (Formula.implication (Formula.variable "b") (Formula.variable "a"))
  -- let formula = parseFormulaWithError "(((a \\/ (a => b))) => b) => b"
  let formula = parseFormulaWithError "b => (a => a)"
  -- let formula = parseFormulaWithError "((((a /\\ b) => c) => ((a => c) \\/ (b => c))) => c) => c"

  IncrementalSolver context solver <- IncrementalSolver.newSolver
  result <- ProverR.proveR context solver formula
  case result of
    ProverR.Invalid counterModel -> putStrLn . ("Result model:\n" ++) =<< CounterModel.counterModelToString context counterModel
    ProverR.Valid (plaindt, clausificationHistory) -> do 
      putStrLn "Valid"
      let carrowNodes = map (\(x, y, z) -> CArrowNode z y x) plaindt
      let (annotatedCArrowNodes, st) = runState (annotateCArrowNodes carrowNodes) newEnvironment

      putStrLn "CARROW:"
      putStrLn $ List.intercalate "\n-------\n" $ map (\(iseq, cseq) -> show cseq ++ "\n%\n" ++ sequentToString (reduceGoal iseq)) annotatedCArrowNodes

      let lastCArrowSeq = fst $ last annotatedCArrowNodes

      let clausificationNodes = map (\(x, y) -> ClausificationNode y x) clausificationHistory 
      let (annotatedClausificationNodes, _) = runState (annotateClausificationNodes lastCArrowSeq clausificationNodes) st

      putStrLn "CLAUSIFICATION:"
      putStrLn $ List.intercalate "\n-------\n" $ map sequentToString annotatedClausificationNodes

      let lastSeq = last annotatedClausificationNodes

      let (goalFormula, goalTerm) = Map.findMin (goal lastSeq)

      putStrLn $ sequentToString lastSeq { goal = Map.singleton goalFormula (reduce goalTerm)} -- $ unlines (map (\(i,c) -> plainSequentToString i ++ " % " ++ show c) carrowNodes)

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
