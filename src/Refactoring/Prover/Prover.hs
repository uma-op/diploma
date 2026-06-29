module Refactoring.Prover.Prover(module Refactoring.Prover.Prover) where

import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map ((!))
import Data.Bifunctor

import Refactoring.Sequent.Unclausified
import Refactoring.Formula.Formula
import Refactoring.Formula
import Refactoring.Sequent.Annotated
import Refactoring.Formula.Atom
import Refactoring.Prover.Clausify
import Refactoring.Sequent.Intuit
import Refactoring.Prover.Solver
import Refactoring.Clause.Flat
import Refactoring.Clause.Impl
import Refactoring.Prover.CArrow
import Refactoring.Prover.LJT
import Refactoring.Utils.Dot
import Refactoring.Prover.Annotate
import qualified Refactoring.Lambda.Lambda as Lambda

import qualified Z3.Base as Z3

import Fmt
import Refactoring.Sequent.Classic (Classic_(Classic))
import Refactoring.Lambda.Lambda (reduce)
import Control.Monad (foldM)

getSequent :: ClausificationRuleII -> Intuit_ () ()
getSequent (AsImpl _ rule _ _ _) = getSequent rule
getSequent (AsFlat _ rule _ _ _) = getSequent rule
getSequent (MakeImpl _ rule _ _ _) = getSequent rule
getSequent (LeftDs _ rule _ _ _) = getSequent rule
getSequent (RightCs _ rule _ _ _) = getSequent rule
getSequent (Uncurry _ rule _ _ _) = getSequent rule
getSequent (Aliasing _ rule _ _ _ _) = getSequent rule
getSequent (ImplImpliesFlat _ rule _ _ _) = getSequent rule
getSequent (FinishClausification _ seq) = seq
getSequent _ = undefined 

prove :: Formula_ -> IO ()
prove formula = do
  let goalAtom = Variable "$"
  let goal = Atom goalAtom
  let sequent = Unclausified [] [] [Annotated () (implication formula goal)] (Annotated ((), ()) goalAtom)
  let (clausified, (ClausificationState _ c1 c2)) = runState (clausify sequent) (ClausificationState 0 Map.empty Map.empty)
  print c1
  print c2

  let (Intuit flats impls goal) = getSequent clausified
  putStrLn $ "Flats created: " ++ (show $ length flats)
  putStrLn $ "Impls created: " ++ (show $ length impls)

  s@(Solver context solver _) <- newSolver

  let universe = Set.toList $ Set.fromList $ annotated goal :
        (atoms =<< (map (toFormula . annotated) flats ++ map (toFormula . annotated) impls))

  putStrLn "Unique atoms"
  print $ length universe

  universeAsts <- mapM (mkFreshAtom context) universe
  let atomToAst = Map.fromList $ zip universe universeAsts

  let reannotatedFlats = Annotated () <$> reannotateFlat (atomToAst !) <$> annotated <$> flats
  initedSolver <- foldM addClause s (annotated <$> reannotatedFlats)

  let reannotatedImpls = Annotated () <$> reannotateImpl (atomToAst !) <$> annotated <$> impls
  let reannotatedGoal = reannotate (((), ) . (atomToAst !)) goal
  let reannotatedIntuit = Intuit reannotatedFlats reannotatedImpls reannotatedGoal

  result <- carrow reannotatedIntuit initedSolver
  case result of  
    Left counterModel -> fmtLn $ counterModel |+ ""
    Right proof -> do
      proof `seq` putStrLn "Proof done"
      let nonAnnotatedProof = second (const ()) proof
      let extended = extendProof nonAnnotatedProof
      let concated = concatTrees clausified (second (const ()) extended)
      let (annotatedProof, env) = runState (annotateClausification concated) (Lambda.Environment 0 Map.empty)
      -- let term (Unclausified _ _ _ (Annotated (t, ()) _)) = t 
      -- let reduced = reduce $ term (rootClausification annotatedProof)
      -- let (extendedTerm, _) = runState (Lambda.extendLambda reduced) env
      -- fmtLn $ extendedTerm |+ ""
      -- fmtLn $ reduced |+ ""
      --   "digraph {\n" <>
      --   "  graph [rankdir=BT]\n" <>
      --   "  node [shape=record;fontname=Arial]\n" <>
      --   indentF 2 (buildDotClausify 0 annotatedProof) <>
      --   "}\n"

      let reducedAnnotatedProof = first Lambda.reduce annotatedProof
      fmtLn $ 
        "digraph {\n" <>
        "  graph [rankdir=BT]\n" <>
        "  node [shape=record;fontname=Arial]\n" <>
        indentF 2 (buildDotClausify 0 reducedAnnotatedProof) <>
        "}\n"

  return ()

  where
    getLJTBranches :: CArrowRule_ () () -> [LJTRule_ () ()]
    getLJTBranches (ExCPL0 iseq ljtBranch _) = [ljtBranch]
    getLJTBranches (ExCPL1 iseq ljtBranch carrowBranch _ _ _) = ljtBranch : getLJTBranches carrowBranch
    getLJTBranches _ = undefined

    mkFreshAtom :: Z3.Context -> Atom_ -> IO Z3.AST
    mkFreshAtom context (Variable vname) = Z3.mkFreshBoolVar context vname
    mkFreshAtom context Bottom = Z3.mkFalse context
    mkFreshAtom context Top = Z3.mkTrue context

    reannotateFlat :: (Atom_ -> Z3.AST) -> Flat_ () -> Flat_ Z3.AST
    reannotateFlat atomToAst (Flat cs ds) = Flat [reannotate atomToAst c | c <- cs] [reannotate atomToAst d | d <- ds]

    reannotateImpl :: (Atom_ -> Z3.AST) -> Impl_ () -> Impl_ Z3.AST
    reannotateImpl atomToAst (Impl a b c) = Impl (reannotate atomToAst a) (reannotate atomToAst b) (reannotate atomToAst c)

    concatTrees :: ClausificationRule_ a c -> CArrowRule_ a c -> ClausificationRule_ a c
    concatTrees (AsImpl s rule x y subs) carrowRule = AsImpl s (concatTrees rule carrowRule) x y subs
    concatTrees (AsFlat s rule x y subs) carrowRule = AsFlat s (concatTrees rule carrowRule) x y subs
    concatTrees (MakeImpl s rule x y subs) carrowRule = MakeImpl s (concatTrees rule carrowRule) x y subs
    concatTrees (LeftDs s rule x y subs) carrowRule = LeftDs s (concatTrees rule carrowRule) x y subs
    concatTrees (RightCs s rule x y subs) carrowRule = RightCs s (concatTrees rule carrowRule) x y subs
    concatTrees (Uncurry s rule x y subs) carrowRule = Uncurry s (concatTrees rule carrowRule) x y subs
    concatTrees (Aliasing s rule x y z subs) carrowRule = Aliasing s (concatTrees rule carrowRule) x y z subs
    concatTrees (ImplImpliesFlat s rule x y subs) carrowRule = ImplImpliesFlat s (concatTrees rule carrowRule) x y subs
    concatTrees (FinishClausification s seq) carrowRule = StartCArrow s carrowRule
    concatTrees _ _ = undefined 


