-- snippet from source
data Environment = Environment {
  cache  :: Map PlainFormula Term,
  vcount :: Int
}

getTermFromEnvironment :: Formula a => a -> State Environment Term
getTermFromEnvironment formula = state newState
  where
    newState env@(Environment cache vcount) =
      case Map.lookup (Formula.plain formula) cache of
        Just term -> (term, env)
        Nothing   -> (Var $ "$" ++ show vcount,
                      env { cache = ..., vcount = vcount + 1 })
