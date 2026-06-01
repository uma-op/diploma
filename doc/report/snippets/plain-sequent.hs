-- snippet from source
data PlainSequent
  = ClassicPlainSequent {
      plainFlats       :: [FlatClauseFormula Atom],
      plainAssumptions :: [Atom],
      plainGoal        :: Atom
    }
  | IntuitPlainSequent {
      plainFlats :: [FlatClauseFormula Atom],
      plainImpls :: [ImplClauseFormula Atom],
      plainGoal  :: Atom
    }
  | UnclausifiedPlainSequent {
      plainFlats        :: [FlatClauseFormula Atom],
      plainImpls        :: [ImplClauseFormula Atom],
      plainUnclausified :: [PlainFormula],
      plainGoal         :: Atom
    }
