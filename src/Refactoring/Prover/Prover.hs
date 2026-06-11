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
import Refactoring.Clause
import Refactoring.Clause.Flat
import Refactoring.Clause.Impl
import Refactoring.Prover.CArrow
import Refactoring.Utils.Dot

import qualified Z3.Base as Z3

import Fmt

getSequent :: ClausificationRuleII -> Intuit_ () ()
getSequent (AsImpl _ rule) = getSequent rule
getSequent (AsFlat _ rule) = getSequent rule
getSequent (MakeImpl _ rule) = getSequent rule
getSequent (LeftDs _ rule) = getSequent rule
getSequent (RightCs _ rule) = getSequent rule
getSequent (Uncurry _ rule) = getSequent rule
getSequent (Aliasing _ rule) = getSequent rule
getSequent (ImplImpliesFlat _ rule) = getSequent rule
getSequent (FinishClausification _ seq) = seq
getSequent _ = undefined 

prove :: Formula_ -> IO ()
prove formula = do
  let goalAtom = Variable "$"
  let goal = Atom goalAtom
  let sequent = Unclausified [] [] [Annotated () (implication formula goal)] (Annotated ((), ()) goalAtom)
  let (clausified, st) = runState (clausify sequent) (ClausificationState 0)
  fmtLn $ buildDotClausify 0 clausified

  let (Intuit flats impls goal) = getSequent clausified

  s@(Solver context solver _) <- newSolver

  let universe = Set.toList $ Set.fromList $ annotated goal :
        (atoms =<< (map (toFormula . annotated) flats ++ map (toFormula . annotated) impls))

  universeAsts <- mapM (mkFreshAtom context) universe
  let atomToAst = Map.fromList $ zip universe universeAsts

  let s = Solver context solver [Annotated (atomToAst ! a) a | a <- universe] 

  let reannotatedFlats = Annotated () <$> reannotateFlat (atomToAst !) <$> annotated <$> flats
  mapM_ (addClause s) (annotated <$> reannotatedFlats)

  let reannotatedImpls = Annotated () <$> reannotateImpl (atomToAst !) <$> annotated <$> impls
  let reannotatedGoal = reannotate (((), ) . (atomToAst !)) goal
  let reannotatedIntuit = Intuit reannotatedFlats reannotatedImpls reannotatedGoal

  result <- carrow reannotatedIntuit s
  case result of  
    Left counterModel -> fmtLn $ counterModel |+ ""
    Right proof -> do
      let extended = extendProof (second (const ()) proof)
      fmtLn $ 
        "digraph {\n" <>
        "  graph [rankdir=BT]\n" <>
        "  node [shape=record;fontname=Arial]\n" <>
        indentF 2 (buildDotClausify 0 $ concatTrees clausified (second (const ()) extended)) <>
        "}\n"

  return ()

  where
    mkFreshAtom :: Z3.Context -> Atom_ -> IO Z3.AST
    mkFreshAtom context (Variable vname) = Z3.mkFreshBoolVar context vname
    mkFreshAtom context Bottom = Z3.mkFalse context
    mkFreshAtom context Top = Z3.mkTrue context

    reannotateFlat :: (Atom_ -> Z3.AST) -> Flat_ () -> Flat_ Z3.AST
    reannotateFlat atomToAst (Flat cs ds) = Flat [reannotate atomToAst c | c <- cs] [reannotate atomToAst d | d <- ds]

    reannotateImpl :: (Atom_ -> Z3.AST) -> Impl_ () -> Impl_ Z3.AST
    reannotateImpl atomToAst (Impl a b c) = Impl (reannotate atomToAst a) (reannotate atomToAst b) (reannotate atomToAst c)

    concatTrees :: ClausificationRule_ a c -> CArrowRule_ a c -> ClausificationRule_ a c
    concatTrees (AsImpl s rule) carrowRule = AsImpl s (concatTrees rule carrowRule) 
    concatTrees (AsFlat s rule) carrowRule = AsFlat s (concatTrees rule carrowRule)
    concatTrees (MakeImpl s rule) carrowRule = MakeImpl s (concatTrees rule carrowRule)
    concatTrees (LeftDs s rule) carrowRule = LeftDs s (concatTrees rule carrowRule)
    concatTrees (RightCs s rule) carrowRule = RightCs s (concatTrees rule carrowRule)
    concatTrees (Uncurry s rule) carrowRule = Uncurry s (concatTrees rule carrowRule)
    concatTrees (Aliasing s rule) carrowRule = Aliasing s (concatTrees rule carrowRule)
    concatTrees (ImplImpliesFlat s rule) carrowRule = ImplImpliesFlat s (concatTrees rule carrowRule)
    concatTrees (FinishClausification s seq) carrowRule = StartCArrow s carrowRule
    concatTrees _ _ = undefined 


