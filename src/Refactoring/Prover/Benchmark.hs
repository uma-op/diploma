module Refactoring.Prover.Benchmark(module Refactoring.Prover.Benchmark) where

import Control.Monad.State
import Data.Bifunctor
import qualified Data.Map as Map
import Data.Map ((!))
import qualified Data.Set as Set
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)
import Control.Monad
import Fmt

import qualified Z3.Base as Z3

import Refactoring.Clause.Flat
import Refactoring.Clause.Impl
import Refactoring.Formula
import Refactoring.Formula.Atom
import Refactoring.Formula.Formula
import Refactoring.Prover.Annotate
import Refactoring.Prover.CArrow
import Refactoring.Prover.Clausify
import Refactoring.Prover.Prover
import Refactoring.Prover.Solver
import Refactoring.Sequent.Annotated
import Refactoring.Sequent.Classic
import Refactoring.Sequent.Intuit
import Refactoring.Sequent.Unclausified
import qualified Refactoring.Lambda.Lambda as Lambda

data BenchmarkOutcome = BenchmarkValid | BenchmarkInvalid
  deriving (Eq, Show)

data BenchmarkResult = BenchmarkResult
  { benchmarkOutcome :: BenchmarkOutcome,
    benchmarkClausificationMs :: Double,
    benchmarkProvingMs :: Double,
    benchmarkAnnotationMs :: Double,
    benchmarkTotalMs :: Double
  }
  deriving (Eq, Show)

data ProvingResult = Proved (CArrowRule_ () ()) | Disproved

proveMeasured :: Formula_ -> IO BenchmarkResult
proveMeasured formula = do
  totalStart <- nowNs

  ((clausified, (flats, impls, goal)), clausificationMs) <- measure $ do
    let goalAtom = Variable "$"
    let goalFormula = Atom goalAtom
    let sequent =
          Unclausified
            []
            []
            [Annotated () (implication formula goalFormula)]
            (Annotated ((), ()) goalAtom)
    let (clausified, _) = runState (clausify sequent) (ClausificationState 0 Map.empty Map.empty)
    let Intuit flats impls goal = getSequent clausified
    length flats `seq` length impls `seq` goal `seq` return (clausified, (flats, impls, goal))

  (proofResult, provingMs) <- measure $ do
    solver@(Solver context _ _) <- newSolver

    let universe =
          Set.toList $
            Set.fromList $
              annotated goal :
              (atoms =<< (map (toFormula . annotated) flats ++ map (toFormula . annotated) impls))

    universeAsts <- mapM (mkFreshAtom context) universe
    let atomToAst = Map.fromList $ zip universe universeAsts

    let reannotatedFlats =
          Annotated () <$> reannotateFlat (atomToAst !) <$> annotated <$> flats
    solverWithUniverse <- foldM addClause solver (annotated <$> reannotatedFlats)

    let reannotatedImpls =
          Annotated () <$> reannotateImpl (atomToAst !) <$> annotated <$> impls
    let reannotatedGoal = reannotate (((), ) . (atomToAst !)) goal
    let reannotatedIntuit = Intuit reannotatedFlats reannotatedImpls reannotatedGoal

    result <- carrow reannotatedIntuit solverWithUniverse
    case result of
      Left _ -> return Disproved
      Right proof -> do
        let plainProof = second (const ()) proof
        forceCArrow plainProof `seq` return (Proved plainProof)

  (outcome, annotationMs) <-
    case proofResult of
      Disproved ->
        return (BenchmarkInvalid, 0)
      Proved proof -> do
        (_, ms) <- measure $ do
          let extended = extendProof proof
          let concated = concatTrees clausified (second (const ()) extended)
          let (annotatedProof, _) =
                runState (annotateClausification concated) (Lambda.Environment 0 Map.empty)
          let term (Unclausified _ _ _ (Annotated (t, ()) _)) = t
          let extractedTerm = term (rootClausification annotatedProof)
          extractedTerm `seq` return extractedTerm
        return (BenchmarkValid, ms)

  totalEnd <- nowNs
  return $
    BenchmarkResult
      { benchmarkOutcome = outcome,
        benchmarkClausificationMs = clausificationMs,
        benchmarkProvingMs = provingMs,
        benchmarkAnnotationMs = annotationMs,
        benchmarkTotalMs = nsToMs (totalEnd - totalStart)
      }

measure :: IO a -> IO (a, Double)
measure action = do
  start <- nowNs
  result <- action
  end <- nowNs
  return (result, nsToMs (end - start))

nowNs :: IO Word64
nowNs = getMonotonicTimeNSec

nsToMs :: Word64 -> Double
nsToMs ns = fromIntegral ns / 1000000.0

mkFreshAtom :: Z3.Context -> Atom_ -> IO Z3.AST
mkFreshAtom context (Variable vname) = Z3.mkFreshBoolVar context vname
mkFreshAtom context Bottom = Z3.mkFalse context
mkFreshAtom context Top = Z3.mkTrue context

reannotateFlat :: (Atom_ -> Z3.AST) -> Flat_ () -> Flat_ Z3.AST
reannotateFlat atomToAst (Flat cs ds) =
  Flat [reannotate atomToAst c | c <- cs] [reannotate atomToAst d | d <- ds]

reannotateImpl :: (Atom_ -> Z3.AST) -> Impl_ () -> Impl_ Z3.AST
reannotateImpl atomToAst (Impl a b c) =
  Impl (reannotate atomToAst a) (reannotate atomToAst b) (reannotate atomToAst c)

forceCArrow :: CArrowRule_ () () -> ()
forceCArrow (CPL0 iseq cseq) = forceIntuit iseq `seq` forceClassic cseq
forceCArrow (CPL1 iseq cseq rule newFlat learnedImpl) =
  forceIntuit iseq `seq`
    forceClassic cseq `seq`
      forceCArrow rule `seq`
        forceFlat newFlat `seq`
          forceImpl learnedImpl
forceCArrow (ExCPL0 iseq ljtRule _) = forceIntuit iseq `seq` ljtRule `seq` ()
forceCArrow (ExCPL1 iseq ljtRule rule newFlat learnedImpl _) =
  forceIntuit iseq `seq`
    ljtRule `seq`
      forceCArrow rule `seq`
        forceFlat newFlat `seq`
          forceImpl learnedImpl

forceIntuit :: Intuit_ () () -> ()
forceIntuit (Intuit flats impls goal) =
  forceAnnotated forceFlat flats `seq`
    forceAnnotated forceImpl impls `seq`
      forceAnnotatedAtom goal

forceClassic :: Classic_ () () -> ()
forceClassic (Classic flats assumptions goal) =
  forceAnnotated forceFlat flats `seq`
    forceAnnotatedAtoms assumptions `seq`
      forceAnnotatedAtom goal

forceFlat :: Flat_ () -> ()
forceFlat (Flat cs ds) = forceAnnotatedAtoms cs `seq` forceAnnotatedAtoms ds

forceImpl :: Impl_ () -> ()
forceImpl (Impl a b c) =
  forceAnnotatedAtom a `seq` forceAnnotatedAtom b `seq` forceAnnotatedAtom c

forceAnnotated :: (b -> ()) -> [Annotated_ a b] -> ()
forceAnnotated _ [] = ()
forceAnnotated force (Annotated annotation value:rest) =
  annotation `seq` force value `seq` forceAnnotated force rest

forceAnnotatedAtom :: Annotated_ a Atom_ -> ()
forceAnnotatedAtom (Annotated annotation atom) = annotation `seq` atom `seq` ()

forceAnnotatedAtoms :: [Annotated_ a Atom_] -> ()
forceAnnotatedAtoms [] = ()
forceAnnotatedAtoms (atom:rest) =
  forceAnnotatedAtom atom `seq` forceAnnotatedAtoms rest

concatTrees :: ClausificationRule_ a c -> CArrowRule_ a c -> ClausificationRule_ a c
concatTrees (AsImpl s rule x y subs) carrowRule = AsImpl s (concatTrees rule carrowRule) x y subs
concatTrees (AsFlat s rule x y subs) carrowRule = AsFlat s (concatTrees rule carrowRule) x y subs
concatTrees (MakeImpl s rule x y subs) carrowRule = MakeImpl s (concatTrees rule carrowRule) x y subs
concatTrees (LeftDs s rule x y subs) carrowRule = LeftDs s (concatTrees rule carrowRule) x y subs
concatTrees (RightCs s rule x y subs) carrowRule = RightCs s (concatTrees rule carrowRule) x y subs
concatTrees (Uncurry s rule x y subs) carrowRule = Uncurry s (concatTrees rule carrowRule) x y subs
concatTrees (Aliasing s rule x y z subs) carrowRule = Aliasing s (concatTrees rule carrowRule) x y z subs
concatTrees (ImplImpliesFlat s rule x y subs) carrowRule = ImplImpliesFlat s (concatTrees rule carrowRule) x y subs
concatTrees (FinishClausification s _) carrowRule = StartCArrow s carrowRule
concatTrees _ _ = undefined
