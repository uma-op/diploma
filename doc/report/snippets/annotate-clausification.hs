-- snippet from source
annotateClausificationNodes seq [] = return [seq]
annotateClausificationNodes seq (h:t) = do
  annotated       <- annotate seq h
  othersAnnotated <- annotateClausificationNodes annotated t
  return (seq : othersAnnotated)
