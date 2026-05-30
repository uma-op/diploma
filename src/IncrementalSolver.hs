module IncrementalSolver where

import qualified Control.Monad as Monad
import qualified Data.List as List
import qualified Z3.Base as Z3

import qualified Clause
import qualified World
import qualified Clausify
import Clause (FlatClauseFormula(..))

data IncrementalSolver = IncrementalSolver
  { context :: Z3.Context,
    solver :: Z3.Solver
  }

newSolver :: IO IncrementalSolver
newSolver = do
  config <- Z3.mkConfig
  Z3.setParamValue config "proof" "true"

  context <- Z3.mkContext config
  solver <- Z3.mkSolver context

  return
    IncrementalSolver
      { context = context,
        solver = solver
      }

initSolver :: Z3.Context -> Z3.Solver -> [FlatClauseFormula Z3.AST] -> IO ()
initSolver context solver = mapM_ (addClause context solver)

addClause :: Z3.Context -> Z3.Solver -> FlatClauseFormula Z3.AST -> IO ()
addClause context solver (FlatClauseFormula cs ds) = do
  and <- Z3.mkAnd context cs
  or <- Z3.mkOr context ds
  implication <- Z3.mkImplies context and or
  Z3.solverAssertCnstr context solver implication

data ProvingResult = Yes [Z3.AST] | No World.World

satProve :: (Z3.FuncDecl -> Z3.AST) -> Z3.Context -> Z3.Solver -> [Z3.AST] -> Z3.AST -> IO ProvingResult
satProve funcDeclToAST context solver adds goal = do
  putStrLn "Sat prove solver:"
  putStrLn . ("Constrs: " ++ ) =<< Z3.solverToString context solver 
  putStrLn . ("Assumptions: " ++ ) . show =<< mapM (Z3.astToString context) adds
  putStrLn . ("Goal: " ++ ) =<< Z3.astToString context goal

  goalAST <- Z3.mkNot context goal
  checkResult <- Z3.solverCheckAssumptions context solver (goalAST : adds)

  case checkResult of
    Z3.Sat -> No <$> (World.fromModel funcDeclToAST context =<< Z3.solverGetModel context solver)
    Z3.Unsat -> Yes . List.delete goalAST <$> Z3.solverGetUnsatCore context solver
    Z3.Undef -> undefined
