-- snippet from source
addClause context solver (FlatClauseFormula cs ds _) = do
  and <- Z3.mkAnd context cs
  or  <- Z3.mkOr context ds
  implication <- Z3.mkImplies context and or
  Z3.solverAssertCnstr context solver implication

satProve funcDeclToAST context solver adds goal = do
  goalAST <- Z3.mkNot context goal
  checkResult <- Z3.solverCheckAssumptions context solver (goalAST : adds)
  case checkResult of
    Z3.Sat   -> No <$> (World.fromModel funcDeclToAST context
                        =<< Z3.solverGetModel context solver)
    Z3.Unsat -> Yes . List.delete goalAST
                <$> Z3.solverGetUnsatCore context solver
