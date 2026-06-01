-- snippet from source
data ValidationResult where
  Valid :: ([(PlainSequent, PlainSequent, CArrowRule)],
            [(PlainSequent, ClausificationRule)]) -> ValidationResult
  Invalid :: CounterModel -> ValidationResult
