-- snippet from source
clausifyLoopS s@(UnclausifiedPlainSequent f i (nph : npt) g) = do
  case Clause.flatClauseFromFormula nph of
    Just clause -> do
      putSequent (s, AsFlat nph clause)
      clausifyLoopS (UnclausifiedPlainSequent (clause:f) i npt g)
    Nothing -> case Clause.implClauseFromFormula nph of
      Just clause -> do
        putSequent (s, AsImpl clause)
        clausifyLoopS (UnclausifiedPlainSequent f (clause:i) npt g)
      Nothing -> do
        (clausified, rule) <- clausifyS nph
        putSequent (s, rule)
        clausifyLoopS (UnclausifiedPlainSequent f i (clausified ++ npt) g)

clausifyLoopS s@(UnclausifiedPlainSequent f i [] g) = do
  putSequent (s, AsIntuit)
  return (IntuitPlainSequent f i g)

putSequent seq = ST.state (\st -> ((), BF.second (seq:) st))
