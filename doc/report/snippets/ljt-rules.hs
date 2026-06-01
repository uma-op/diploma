-- snippet from source
data LJTNode =
  Axiom PlainSequent |
  Cs PlainSequent LJTNode (FlatClauseFormula Atom, FlatClauseFormula Atom, Atom) |
  Ds PlainSequent [LJTNode] (FlatClauseFormula Atom)

proveLJT pseq =
  case applyAxiom pseq of
    Just () -> Axiom pseq
    Nothing -> case applyCs pseq of
      Just (newPseq, keyF, newF, atom) -> Cs pseq (proveLJT newPseq) (keyF, newF, atom)
      Nothing -> case applyDs pseq of
        Just (newPseqs, keyF) -> Ds pseq (map proveLJT newPseqs) keyF
        Nothing -> error "Wrong sequent"
