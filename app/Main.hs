module Main(main) where

import Data.Maybe
import Control.Monad.State
import Data.Functor
import Z3.Base
import Data.Bifunctor

import qualified ProverR
import qualified World
import Proof

import IncrementalSolver(IncrementalSolver(..))
import qualified IncrementalSolver

import qualified CounterModel
import Parser (parseFormula, parseFormulaWithError)
import Sequent
import Clause
import Formula
import ClassicSeqProver

-- main :: IO ()
-- main = do
--   config <- mkConfig
--   setParamValue config "proof" "true"
--   context <- mkContext config
--   solver <- mkSolver context
-- 
--   a <- mkFreshBoolVar context "a"
--   b <- mkFreshBoolVar context "b"
-- 
--   lhs <- mkImplies context a b 
--   rhs <- mkImplies context b =<< mkFalse context
-- 
--   solverAssertCnstr context solver a
--   solverAssertCnstr context solver lhs
--   solverAssertCnstr context solver rhs
--   result <- solverCheck context solver
--   print result
--   proof <- solverGetProof context solver
--   putStrLn =<< astToString context proof


main :: IO ()
main = do
  test2

test2 :: IO ()
test2 = do
  -- let formula = Formula.disjunction (Formula.variable "a") (Formula.negation $ Formula.variable "a")
  -- let formula = Formula.disjunction
  --                 (Formula.implication (Formula.variable "a") (Formula.variable "b"))
  --                 (Formula.implication (Formula.variable "b") (Formula.variable "a"))
  let formula = parseFormulaWithError "(((a \\/ (a => b))) => b) => b"
  -- let formula = parseFormulaWithError "b => (a => a)"
  -- let formula = parseFormulaWithError "((((a /\\ b) => c) => ((a => c) \\/ (b => c))) => c) => c"

  IncrementalSolver context solver <- IncrementalSolver.newSolver
  result <- ProverR.proveR context solver formula
  case result of
    ProverR.Invalid counterModel -> putStrLn . ("Result model:\n" ++) =<< CounterModel.counterModelToString context counterModel
    ProverR.Valid (plaindt, clausificationHistory) -> do 
      putStrLn "Valid"
      let carrowNodes = map (\(x, y, z) -> CArrowNode z y x) plaindt
      let annotatedIntuitSeq = annotateCArrowNodes carrowNodes
      let annotatedClausifiedSeq = undefined

      putStrLn  "Hello" -- $ unlines (map (\(i,c) -> plainSequentToString i ++ " % " ++ show c) carrowNodes)

test :: IO ()
test = do
  let s = ClassicPlainSequent
        [
          FlatClauseFormula [Variable "a"] [Variable "b"],
          FlatClauseFormula [Variable "b"] [Variable "g"],
          FlatClauseFormula [Variable "b"] [Variable "b"]
        ]
        [
          Variable "a"
        ]
        (Variable "b") 

  let classicDT = proveLJT s
  print classicDT

  let (annotated, _) = runState (annotateLJTNode classicDT) newEnvironment
  putStrLn (sequentToString annotated)

  return undefined

