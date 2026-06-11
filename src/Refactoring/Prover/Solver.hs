module Refactoring.Prover.Solver(module Refactoring.Prover.Solver) where

import qualified Data.List as List
import qualified Data.Maybe as Maybe
import qualified Data.Map as Map
import Data.Map ((!))

import Refactoring.Clause.Flat
import Refactoring.Formula.Atom

import qualified Z3.Base as Z3
import Refactoring.Sequent.Annotated
import Fmt

data Solver_ =
  Solver
    Z3.Context
    Z3.Solver
    [Annotated_ Z3.AST Atom_]

newSolver :: IO Solver_
newSolver = do
  config <- Z3.mkConfig
  Z3.setParamValue config "proof" "true"

  context <- Z3.mkContext config
  solver <- Z3.mkSolver context

  return $ Solver context solver []

addClause :: Solver_ -> Flat_ Z3.AST -> IO ()
addClause (Solver context solver universe) (Flat cs ds) = do
  csAST <- Z3.mkAnd context $ annotation <$> cs
  dsAST <- Z3.mkOr context $ annotation <$> ds
  clauseAST <- Z3.mkImplies context csAST dsAST

  Z3.solverAssertCnstr context solver clauseAST

data SatProveResult_ = Yes [Annotated_ Z3.AST Atom_] | No [Annotated_ Z3.AST Atom_]

satProve :: Solver_ -> [Annotated_ Z3.AST Atom_] -> Annotated_ ((), Z3.AST) Atom_ -> IO SatProveResult_
satProve (Solver context solver universe) assumptions goal = do
  notGoal <- Z3.mkNot context (snd $ annotation goal)
  result <- Z3.solverCheckAssumptions context solver (notGoal : map annotation assumptions)
  case result of
    Z3.Unsat -> do
      core <- List.delete notGoal <$> Z3.solverGetUnsatCore context solver
      let astMap = Map.fromList [(ast, ann) | ann@(Annotated ast _) <- assumptions]
      return $ Yes [astMap ! ast | ast <- core]
    Z3.Sat -> do
      model <- Z3.solverGetModel context solver
      universeValues <- Maybe.catMaybes <$> mapM (Z3.evalBool context model) (map annotation universe)
      return $ No [ast | (ast, val) <- zip universe universeValues, val]

    Z3.Undef -> undefined
