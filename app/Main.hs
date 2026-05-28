module Main(main) where

import Data.Maybe
import Data.Functor
import Z3.Base

import qualified ProverR
import qualified Formula
import qualified World

import IncrementalSolver(IncrementalSolver(..))
import qualified IncrementalSolver

import qualified CounterModel
import Parser (parseFormula, parseFormulaWithError)

main :: IO ()
main = do
  config <- mkConfig
  setParamValue config "proof" "true"
  context <- mkContext config
  solver <- mkSolver context

  a <- mkFreshBoolVar context "a"
  b <- mkFreshBoolVar context "b"

  lhs <- mkImplies context a b 
  rhs <- mkImplies context b a
  solverAssertCnstr context solver =<< mkImplies context lhs rhs
  solverAssertCnstr context solver b
  solverAssertCnstr context solver =<< mkNot context a
  result <- solverCheck context solver
  print result
  proof <- solverGetProof context solver
  putStrLn =<< astToString context proof


-- main :: IO ()
-- main = do
--   -- let formula = Formula.disjunction (Formula.variable "a") (Formula.negation $ Formula.variable "a")
--   -- let formula = Formula.disjunction
--   --                 (Formula.implication (Formula.variable "a") (Formula.variable "b"))
--   --                 (Formula.implication (Formula.variable "b") (Formula.variable "a"))
--   -- let formula = parseFormulaWithError "(((a \\/ (a => b))) => b) => b"
--   let formula = parseFormulaWithError "b => (a => a)"
--   -- let formula = parseFormulaWithError "((((a /\\ b) => c) => ((a => c) \\/ (b => c))) => c) => c"
-- 
--   IncrementalSolver context solver <- IncrementalSolver.newSolver
--   result <- ProverR.proveR context solver formula
--   case result of
--     ProverR.Invalid counterModel -> putStrLn . ("Result model:\n" ++) =<< CounterModel.counterModelToString context counterModel
--     ProverR.Valid -> putStrLn "Valid"

