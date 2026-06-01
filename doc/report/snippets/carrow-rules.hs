-- snippet from source
data CArrowRule = CPL0 | CPL1 (FlatClauseFormula Atom) (ImplClauseFormula Atom)

data CArrowNode = CArrowNode {
  carrowRule      :: CArrowRule,
  classicSequent  :: PlainSequent,
  implSequent     :: PlainSequent
}
