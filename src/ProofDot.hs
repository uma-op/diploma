module ProofDot
  ( ljtToDot
  , cArrowClausificationToDot
  ) where

import Control.Monad.State

import ClassicSeqProver (AnnotatedLJTNode(..))
import Proof (CArrowRule(..), ClausificationRule)
import Sequent (Sequent, sequentToString)

type DotLines = [String]

escapeDotLabel :: String -> String
escapeDotLabel = concatMap escapeChar
  where
    escapeChar '\\' = "\\\\"
    escapeChar '"' = "\\\""
    escapeChar '\n' = "\\n"
    escapeChar c = [c]

sequentLabel :: Sequent -> String
sequentLabel = escapeDotLabel . sequentToString

wrapDigraph :: String -> DotLines -> String
wrapDigraph name body =
  unlines
    ( ("digraph " ++ name ++ " {")
    : "  graph [rankdir=BT];"
    : "  node [shape=box];"
    : body
    ++ ["}"]
    )

nodeLine :: String -> String -> String
nodeLine nodeId label = "  " ++ nodeId ++ " [label=\"" ++ label ++ "\"];"

edgeLine :: String -> String -> String -> String
edgeLine from to label = "  " ++ from ++ " -> " ++ to ++ " [label=\"" ++ label ++ "\"];"

showCArrowRule :: CArrowRule -> String
showCArrowRule CPL0 = "CPL0"
showCArrowRule CPL1{} = "CPL1"

ljtToDot :: Int -> AnnotatedLJTNode -> String
ljtToDot index ljtNode =
  let ((_, lines), _) = runState (buildLJT "ljt" ljtNode) (0 :: Int)
  in wrapDigraph ("LJT_" ++ show index) lines

buildLJT :: String -> AnnotatedLJTNode -> State Int (String, DotLines)
buildLJT prefix node = do
  nodeId <- freshId prefix
  case node of
    AnnotatedAxiom seq ->
      return (nodeId, [nodeLine nodeId ("Ax\\n" ++ sequentLabel seq)])
    AnnotatedCs seq branch _ -> do
      (childId, childLines) <- buildLJT (nodeId ++ "_") branch
      let label = "Cs\\n" ++ sequentLabel seq
      return
        ( nodeId
        , nodeLine nodeId label
          : edgeLine nodeId childId "Cs"
          : childLines
        )
    AnnotatedDs seq branches _ -> do
      branchRoots <- mapM (buildLJT (nodeId ++ "_")) branches
      let label = "Ds\\n" ++ sequentLabel seq
      let edges = [edgeLine nodeId childId "Ds" | (childId, _) <- branchRoots]
      return
        ( nodeId
        , nodeLine nodeId label : edges ++ concatMap snd branchRoots
        )
  where
    freshId p = do
      n <- get
      put (n + 1)
      return (p ++ show n)

cArrowClausificationToDot
  :: [CArrowRule]
  -> [(Sequent, AnnotatedLJTNode)]
  -> [ClausificationRule]
  -> [Sequent]
  -> String
cArrowClausificationToDot carrowRules carrowNodes clRules clSequents =
  wrapDigraph "Proof" (fst (runState (buildCArrowClausification carrowRules carrowNodes clRules clSequents) (0 :: Int)))

buildCArrowClausification
  :: [CArrowRule]
  -> [(Sequent, AnnotatedLJTNode)]
  -> [ClausificationRule]
  -> [Sequent]
  -> State Int DotLines
buildCArrowClausification carrowRules carrowNodes clRules clSequents = do
  (cArrowLines, lastCArrowId) <- buildCArrowWithLastId carrowRules carrowNodes
  let clLines = buildClausificationExtension lastCArrowId clRules clSequents
  return (cArrowLines ++ clLines)

buildCArrowWithLastId
  :: [CArrowRule]
  -> [(Sequent, AnnotatedLJTNode)]
  -> State Int (DotLines, String)
buildCArrowWithLastId rules nodes = do
  built <- mapM buildNode (zip rules nodes)
  let rootIds = map fst built
  return (concatMap snd built ++ chainEdges rootIds, last rootIds)
  where
    buildNode (rule, (sequent, ljt)) = do
      nodeId <- freshId "ca"
      (ljtRootId, ljtLines) <- buildLJT (nodeId ++ "_ljt_") ljt
      let nodeLabel = showCArrowRule rule ++ "\\n" ++ sequentLabel sequent
      return
        ( nodeId
        , nodeLine nodeId nodeLabel
          : edgeLine nodeId ljtRootId "left"
          : ljtLines
        )

    chainEdges [] = []
    chainEdges [_] = []
    chainEdges (rootId1 : rootId2 : rest) =
      edgeLine rootId2 rootId1 "right" : chainEdges (rootId2 : rest)

    freshId p = do
      n <- get
      put (n + 1)
      return (p ++ show n)

buildClausificationExtension
  :: String
  -> [ClausificationRule]
  -> [Sequent]
  -> DotLines
buildClausificationExtension startNodeId rules sequents =
  let restSequents = drop 1 sequents
      nodeIds = map (("cl" ++) . show) [1 .. length restSequents]
      nodeLines = [nodeLine nodeId (sequentLabel seq) | (nodeId, seq) <- zip nodeIds restSequents]
   in nodeLines ++ clausificationEdges startNodeId nodeIds rules
  where
    clausificationEdges _ [] _ = []
    clausificationEdges startNodeId nodeIds rules =
      [ edgeLine from to (escapeDotLabel (show rule))
      | (from, to, rule) <- zip3 nodeIds (startNodeId : init nodeIds) rules
      ]
