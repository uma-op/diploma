-- snippet from source
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
    ProverR.Invalid counterModel -> ...
    ProverR.Valid (plaindt, clausificationHistory) -> do
      let (annotatedCArrowNodes, st) =
            runState (annotateCArrowNodes carrowNodes) newEnvironment
      let (annotatedClausificationNodes, _) =
            runState (annotateClausificationNodes lastCArrowSeq
                      clausificationNodes) st
      ...
