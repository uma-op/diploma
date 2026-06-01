-- snippet from source
annotateCPL0 (CArrowNode CPL0 cseq iseq@(IntuitPlainSequent _ impls _)) = do
  let provedCseq = proveLJT cseq
  annotatedClassic <- annotateLJTNode provedCseq
  let (ClassicSequent flats assumptions goal) = rootLJT annotatedClassic
  implAnnotations <- mapM getTermFromEnvironment impls
  return (IntuitSequent {
    flats = flats,
    impls = Map.fromList $ zip impls implAnnotations,
    goal  = goal
  }, annotatedClassic)
