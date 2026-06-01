-- snippet from source
fromModel funcDeclToAST context model = do
  constDecls <- Z3.getConsts context model
  interps    <- catMaybes <$> mapM (Z3.getConstInterp context model) constDecls
  interpValues <- mapM (Z3.getBool context) interps
  let astToValues = zip (map funcDeclToAST constDecls) interpValues
  return World {
    model  = model,
    consts = Set.fromList [ast | (ast, True) <- astToValues]
  }
