-- snippet from source
data CounterModel = CounterModel {
  reachableTo   :: Map Int [Int],
  reachableFrom :: Map Int [Int],
  worlds        :: Map Int World
}

selectWorld counterModel impl = ...
  -- snippet from source

counterModelToDot context counterModel = do
  ...
  return $ unlines
    ( "digraph CounterModel {"
    : "  graph [rankdir=BT];"
    : nodeLines ++ edgeLines ++ ["}"])
