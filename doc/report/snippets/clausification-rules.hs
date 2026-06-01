-- snippet from source
data ClausificationRule =
  MakeImpl PlainFormula PlainFormula |
  LeftDs PlainFormula [PlainFormula] |
  RightCs PlainFormula [PlainFormula] |
  RightImpl PlainFormula PlainFormula |
  Aliasing PlainFormula PlainFormula [PlainFormula] |
  ImplImpliesFlat (ImplClauseFormula Atom) (FlatClauseFormula Atom) |
  AsFlat PlainFormula (FlatClauseFormula Atom) |
  AsImpl (ImplClauseFormula Atom) |
  AsIntuit
