-- snippet from source
annotate seq (ClausificationNode (AsFlat f c) _) = do
  let f'Term = fs ! c
  fTerm <- getNewTermFromEnvironment
  substitution <- case f of
    (Atom _) ->
      Abstraction [varName capture] $ Application [Sum 1, fTerm]
    (Implication [Atom _, Atom _]) ->
      Abstraction [varName capture] $
        Application [Sum 1, Application [fTerm, Application [Proj 1, capture]]]
    (Implication [Atom _, Disjunction ds]) -> ...
    (Implication [Conjunction cs, Atom _]) -> ...
  return seq {
    flats        = Map.delete c fs,
    unclausified = Map.insert f fTerm ucs,
    goal         = applyLocalGoalSubstitution (varName f'Term) substitution g
  }
