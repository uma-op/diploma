-- snippet from source
data AnnotatedGoal = AnnotatedGoal {
  goalTerm          :: Term,
  goalSubstitutions :: [(String, Term)]
}

formatGoal goal =
  let (goalFormula, AnnotatedGoal term substitutions) = Map.findMin goal
  in formulaToString goalFormula ++ "\n" ++ show (reduce term)
     ++ unlines (map (\(n, t) -> n ++ " / " ++ show t) substitutions)

goalPreserveTerm goal =
  let (atom, AnnotatedGoal term _) = Map.findMin goal
  in singletonGoal atom term   -- snippet from source
