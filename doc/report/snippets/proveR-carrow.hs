-- snippet from source
proveR' rootSeq@(IntuitPlainSequent r x g) plainDt = do
  result <- IncrementalSolver.satProve funcDeclToAST context solver [] goalAST
  case result of
    IncrementalSolver.Yes a ->
      return $ Valid ((rootSeq, ClassicPlainSequent r (map astToVar a) g, CPL0)
                      :plainDt, history)
    IncrementalSolver.No m -> do
      result <- proveR'' implsAST (CounterModel.newCounterModel m)
      case result of
        Left (assumptions, impl) -> do
          let newClause = FlatClauseFormula
                (List.delete (a_ impl) assumptions) [c_ impl] ...
          IncrementalSolver.addClause context solver newClause
          proveR' (IntuitPlainSequent (newClauseFormula:r) x g)
            ((rootSeq, ClassicPlainSequent r (map astToVar assumptions)
              (astToVar $ b_ impl), CPL1 newClauseFormula learnedClauseFormula)
             :plainDt)
        Right counterModel -> return $ Invalid counterModel
