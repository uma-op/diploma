-- snippet from source
varToASTMap <- sequence $ Map.fromSet (Formula.atomToAST context) vars
let varToAST = (!) varToASTMap
let astToVar = (!) (Map.fromList $ map swap $ Map.toList varToASTMap)

funcDeclToASTMap <-
  Map.fromList <$>
  mapM (\ast -> (,ast) <$> (Z3.getAppDecl context =<< Z3.toApp context ast))
  (Map.elems varToASTMap)

let funcDeclToAST = (!) funcDeclToASTMap
