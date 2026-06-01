-- snippet from source
implications = do ds <- disjunctions
                is' <- implications'
                return $ Foldable.foldr1 implication (ds:is')

disjunctions = ...   -- snippet from source
conjunctions = ...   -- snippet from source
negations    = do negationSign
                   flip implication bottom <$> negations
              <|> unit
