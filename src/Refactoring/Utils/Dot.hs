module Refactoring.Utils.Dot(module Refactoring.Utils.Dot) where

import Data.Foldable
import Refactoring.Formula.Formula
import Refactoring.Formula.Atom
import Refactoring.Utils.Formatting
import Refactoring.Clause.Flat
import Refactoring.Clause.Impl
import Refactoring.Sequent.Unclausified
import Refactoring.Sequent.Intuit
import Refactoring.Sequent.Classic
import Refactoring.Sequent.Annotated
import Refactoring.Prover.Clausify
import Refactoring.Prover.CArrow
import Refactoring.Prover.LJT
import qualified Refactoring.Lambda.Lambda as Lambda

import Fmt

class BuildableDot a where
  buildDot :: a -> Builder

class BuildableDotAnnotation a where
  buildDotAnnotation :: a -> Builder

instance {-# OVERLAPPING #-} BuildableDotAnnotation () where
  buildDotAnnotation _ = ""

instance {-# OVERLAPPING #-} (BuildableDotAnnotation a, BuildableDotAnnotation b) => BuildableDotAnnotation (a, b) where
  buildDotAnnotation (a, b) = buildDotAnnotation a <> buildDotAnnotation b

instance {-# OVERLAPPABLE #-} BuildableDot a => BuildableDotAnnotation a where
  buildDotAnnotation a = buildDot a <> ": "

instance (BuildableDotAnnotation a, BuildableDot b) => BuildableDot (Annotated_ a b) where
  buildDot (Annotated a b) = buildDotAnnotation a <> buildDot b

instance BuildableDot Atom_ where
  buildDot (Variable vname) = vname |+ ""
  buildDot Top = "$top;"
  buildDot Bottom = "$perp;"

instance BuildableDot Formula_ where
  buildDot (Implication is) = "(" <> joinBy " &rarr; " (buildDot <$> is) <> ")"
  buildDot (Conjunction cs) = "(" <> joinBy " &and; " (buildDot <$> cs) <> ")"
  buildDot (Disjunction ds) = "(" <> joinBy " &or; " (buildDot <$> ds) <> ")"
  buildDot (Atom a) = buildDot a

instance BuildableDot (Flat_ a) where
  buildDot (Flat cs ds) =
    joinBy " &and; " (buildDot <$> annotated <$> cs) <> " &rarr; " <>
    joinBy " &or; " (buildDot <$> annotated <$> ds)

instance BuildableDot (Impl_ a) where
  buildDot (Impl a b c) =
    "(" <> (buildDot $ annotated a) <> " &rarr; " <>
    (buildDot $ annotated b) <> ") &rarr; " <>
    (buildDot $ annotated c) <> ""

instance (BuildableDotAnnotation a, BuildableDotAnnotation c) => BuildableDot (Unclausified_ a c) where
  buildDot (Unclausified flats impls uncs goal) =
    "{{R|" <> joinBy "\\n" (buildDot <$> flats) <>
    "}|{X|" <> joinBy "\\n" (buildDot <$> impls) <>
    "}|{U|" <> joinBy "\\n" (buildDot <$> uncs) <>
    "}|" <> buildDot goal <> "}"

instance (BuildableDotAnnotation a, BuildableDotAnnotation c) => BuildableDot (Intuit_ a c) where
  buildDot (Intuit flats impls goal) =
    "{{R|" <> joinBy "\\n" (buildDot <$> flats) <>
    "}|{X|" <> joinBy "\\n" (buildDot <$> impls) <>
    "}|" <> buildDot goal <> "}"

instance (BuildableDotAnnotation a, BuildableDotAnnotation c) => BuildableDot (Classic_ a c) where
  buildDot (Classic flats assumptions goal) =
    "{{R|" <> joinBy "\\n" (buildDot <$> flats) <>
    "}|{A|" <> joinBy "\\n" (buildDot <$> assumptions) <>
    "}|" <> buildDot goal <> "}"

buildDotClausify :: (BuildableDotAnnotation a, BuildableDotAnnotation c) => Int -> ClausificationRule_ a c -> Builder
buildDotClausify rootNodeId (AsImpl c r _ _ subs) = 
  rootNodeId |+ " [label=\"" <> buildDot c <> "|{" <> joinBy "\\n" (buildDot <$> subs) <> "}\"]\n" +|
  rootNodeId |+ " -> " +| (rootNodeId + 1) |+ " [label=AsImpl]\n" <>
  (buildDotClausify (rootNodeId + 1) r)
buildDotClausify rootNodeId (AsFlat c r _ _ subs) = 
  rootNodeId |+ " [label=\"" <> buildDot c <> "|{" <> joinBy "\\n" (buildDot <$> subs) <> "}\"]\n" +|
  rootNodeId |+ " -> " +| (rootNodeId + 1) |+ " [label=AsFlat]\n" <>
  (buildDotClausify (rootNodeId + 1) r)
buildDotClausify rootNodeId (ImplImpliesFlat c r _ _ subs) = 
  rootNodeId |+ " [label=\"" <> buildDot c <> "|{" <> joinBy "\\n" (buildDot <$> subs) <> "}\"]\n" +|
  rootNodeId |+ " -> " +| (rootNodeId + 1) |+ " [label=ImplImpliesFlat]\n" <>
  (buildDotClausify (rootNodeId + 1) r)
buildDotClausify rootNodeId (MakeImpl c r _ _ subs) = 
  rootNodeId |+ " [label=\"" <> buildDot c <> "|{" <> joinBy "\\n" (buildDot <$> subs) <> "}\"]\n" +|
  rootNodeId |+ " -> " +| (rootNodeId + 1) |+ " [label=MakeImpl]\n" <>
  (buildDotClausify (rootNodeId + 1) r)
buildDotClausify rootNodeId (LeftDs c r _ _ subs) = 
  rootNodeId |+ " [label=\"" <> buildDot c <> "|{" <> joinBy "\\n" (buildDot <$> subs) <> "}\"]\n" +|
  rootNodeId |+ " -> " +| (rootNodeId + 1) |+ " [label=LeftDs]\n" <>
  (buildDotClausify (rootNodeId + 1) r)
buildDotClausify rootNodeId (RightCs c r _ _ subs) = 
  rootNodeId |+ " [label=\"" <> buildDot c <> "|{" <> joinBy "\\n" (buildDot <$> subs) <> "}\"]\n" +|
  rootNodeId |+ " -> " +| (rootNodeId + 1) |+ " [label=RightCs]\n" <>
  (buildDotClausify (rootNodeId + 1) r)
buildDotClausify rootNodeId (Uncurry c r _ _ subs) = 
  rootNodeId |+ " [label=\"" <> buildDot c <> "|{" <> joinBy "\\n" (buildDot <$> subs) <> "}\"]\n" +|
  rootNodeId |+ " -> " +| (rootNodeId + 1) |+ " [label=Uncurry]\n" <>
  (buildDotClausify (rootNodeId + 1) r)
buildDotClausify rootNodeId (Aliasing c r _ _ _ subs) = 
  rootNodeId |+ " [label=\"" <> buildDot c <> "|{" <> joinBy "\\n" (buildDot <$> subs) <> "}\"]\n" +|
  rootNodeId |+ " -> " +| (rootNodeId + 1) |+ " [label=Aliasing]\n" <>
  (buildDotClausify (rootNodeId + 1) r)
buildDotClausify rootNodeId (FinishClausification c i) = 
  rootNodeId |+ " [label=\"" <> buildDot c <> "\"]\n" +|
  (rootNodeId + 1) |+ " [label=\"" <> buildDot i <> "\"]\n" +|
  rootNodeId |+ " -> " +| (rootNodeId + 1) |+ " [label=FinishClausification]\n"
buildDotClausify rootNodeId (StartCArrow c r) = 
  rootNodeId |+ " [label=\"" <> buildDot c <> "\"]\n" +|
  rootNodeId |+ " -> " +| (rootNodeId + 1) |+ " [label=StartCArrow]\n" <>
  buildDotCArrow (rootNodeId + 1) r

buildDotCArrow :: (BuildableDotAnnotation a, BuildableDotAnnotation c) => Int -> CArrowRule_ a c -> Builder
buildDotCArrow rootNodeId (CPL0 iseq cseq) =
  rootNodeId |+ " [label=\"" <> buildDot iseq <> "\"]\n" +|
  (rootNodeId + 1) |+ " [label=\"" <> buildDot cseq <> "\"]\n" +|
  rootNodeId |+ " -> " +| (rootNodeId + 1) |+ " [label=CPL0]\n"
buildDotCArrow rootNodeId (CPL1 iseq cseq r _ _) =
  rootNodeId |+ " [label=\"" <> buildDot iseq <> "\"]\n" +|
  (rootNodeId + 1) |+ " [label=\"" <> buildDot cseq <> "\"]\n" +|
  rootNodeId |+ " -> " +| (rootNodeId + 1) |+ " [label=CPL1]\n" +|
  rootNodeId |+ " -> " +| (rootNodeId + 2) |+ " [label=CPL1]\n" <>
  buildDotCArrow (rootNodeId + 2) r
buildDotCArrow rootNodeId (ExCPL0 iseq ljtRule subs) =
  rootNodeId |+ " [label=\"" <> buildDot iseq <> "|{" <> joinBy "\\n" (buildDot <$> subs) <> "}\"]\n" <>
  buildDotLJT rootNodeId [0] ljtRule +|
  rootNodeId |+ " -> \"" +| rootNodeId |+ "_0\" [label=CPL0]\n"
buildDotCArrow rootNodeId (ExCPL1 iseq ljtRule rule _ _ subs) =
  rootNodeId |+ " [label=\"" <> buildDot iseq <> "|{" <> joinBy "\\n" (buildDot <$> subs) <> "}\"]\n" <>
  buildDotLJT rootNodeId [0] ljtRule +|
  rootNodeId |+ " -> \"" +| rootNodeId |+ "_0\" [label=CPL1]\n" +|
  rootNodeId |+ " -> " +| (rootNodeId + 1) |+ " [label=CPL1]\n" <>
  buildDotCArrow (rootNodeId + 1) rule

buildDotLJT :: (BuildableDotAnnotation a, BuildableDotAnnotation c) => Int -> [Int] -> LJTRule_ a c -> Builder
buildDotLJT carrowRootId rootNodeIds (Axiom cseq) =
  "\"" +| carrowRootId |+ "_" +| joinBy "_" rootNodeIds |+ "\" [label=\"" <> buildDot cseq <> "\"]\n"

buildDotLJT carrowRootId rootNodeIds (ReduceConjunction cseq rule _ _ subs) =
  buildedIds |+ " [label=\"" <> buildDot cseq <> "|{" <> joinBy "\\n" (buildDot <$> subs) <> "}\"]\n" <>
  buildedIds |+ " -> \"" +| carrowRootId |+ "_" +| joinBy "_" newLJTIds <> "\" [label=ReduceConjunction]\n" <>
  buildDotLJT carrowRootId newLJTIds rule
  where
    buildedIds = "\"" <> (carrowRootId |+ "_") <> joinBy "_" rootNodeIds <> "\""
    newLJTIds = (head rootNodeIds + 1 : tail rootNodeIds)

buildDotLJT carrowRootId rootNodeIds (SplitDisjunction cseq rules _ subs) =
  buildedIds |+ " [label=\"" <> buildDot cseq <> "|{" <> joinBy "\\n" (buildDot <$> subs) <> "}\"]\n" <> trees <> edges
  where
    buildedIds = "\"" <> (carrowRootId |+ "_") <> joinBy "_" rootNodeIds <> "\""
    newNodeIds = [(0 : i : rootNodeIds) | (i, _) <- zip [0..] rules]
    trees = fold [buildDotLJT carrowRootId newNodeId rule | (newNodeId, rule) <- zip newNodeIds rules]
    edges = fold [
      buildedIds <> (" -> \"" +| carrowRootId |+ "_" +| joinBy "_" newNodeId |+ "\" [label=SplitDisjunction]\n")
      | newNodeId <- newNodeIds]

instance BuildableDot Lambda.Lambda_ where
  buildDot = build

instance BuildableDot Lambda.Substitution_ where
  buildDot (Lambda.Substitution capture arg) = capture |+ " ~ " +| arg |+ ""

