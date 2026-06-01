-- snippet from source
clausifyS f@(Implication [Disjunction ds, v@(Atom _)]) = do
  let newFormulas = map (`implication` v) ds
  return (newFormulas, LeftDs f newFormulas)

clausifyS f@(Implication [v@(Atom _), Conjunction cs]) = do
  let newFormulas = map (implication v) cs
  return (newFormulas, RightCs f newFormulas)

clausifyS f@(Implication (x : y : z : is)) = do
  let newFormula = Implication (conjunction x y : z : is)
  return ([newFormula], RightImpl f newFormula)

clausifyS x = do
  let newFormula = implication top x
  return ([newFormula], MakeImpl x newFormula)
