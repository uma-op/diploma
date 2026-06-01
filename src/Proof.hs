{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-binds #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE TupleSections #-}

module Proof where

import Data.Void
import Data.Map(Map, (!))
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Control.Monad.State
import qualified Data.List as List
import Control.Monad
import Debug.Trace

import Formula
import Clause
import Sequent
import Term
import ClassicSeqProver

type ClassicProof = Void 

data ClausificationRule =
  MakeImpl PlainFormula PlainFormula |
  LeftDs PlainFormula [PlainFormula] |
  RightCs PlainFormula [PlainFormula] |
  RightImpl PlainFormula PlainFormula |
  Aliasing PlainFormula PlainFormula [PlainFormula] |
  ImplImpliesFlat (ImplClauseFormula Atom) (FlatClauseFormula Atom) | 

  AsFlat PlainFormula (FlatClauseFormula Atom) |
  AsImpl (ImplClauseFormula Atom) |
  AsIntuit

instance Show ClausificationRule where
  show MakeImpl{} = "MakeImpl"
  show LeftDs{} = "LeftDs"
  show RightCs{} = "RightCs"
  show RightImpl{} = "RightImpl"
  show Aliasing{} = "Aliasing"
  show AsFlat{} = "AsFlat"
  show AsImpl{} = "AsImpl"
  show AsIntuit{} = "AsIntuit"
  show ImplImpliesFlat{} = "ImplImpliesFlat"

data ClausificationNode = ClausificationNode {
  clausificationRule :: ClausificationRule,
  unclausifiedSequent :: PlainSequent
}

annotateClausificationNodes :: Sequent -> [ClausificationNode] -> State Environment [Sequent]
annotateClausificationNodes seq [] = return [seq]
annotateClausificationNodes seq (h:t) = do 
  annotated <- annotate seq h
  othersAnnotated <- annotateClausificationNodes annotated t
  return (seq : othersAnnotated) 
  where
    annotate :: Sequent -> ClausificationNode -> State Environment Sequent
    annotate
      seq@(UnclausifiedSequent fs is ucs g)
      (ClausificationNode (MakeImpl x f) _) = do
      xTerm <- getTermFromEnvironment x
      return seq {
        unclausified = Map.insert x xTerm $ Map.delete f ucs,
        goal = applyLocalGoalSubstitution (varName (ucs ! f)) (Const xTerm) g
      }
    annotate  
      seq@(UnclausifiedSequent fs is ucs g)
      (ClausificationNode (LeftDs f vars) _) = do
      fTerm <- getTermFromEnvironment f
      let varsCount = length vars 
      varCaptureTerms <- zip [1..] <$> replicateM varsCount getNewTermFromEnvironment
      let varTerms = map (\(i, t) -> Abstraction [varName t] $ Application [fTerm, Application [Sum i, t]]) varCaptureTerms
      let substitution = zip (map (varName . (ucs !)) vars) varTerms
      return seq {
        unclausified = Map.insert f fTerm (foldr Map.delete ucs vars),
        goal = applyLocalGoalSubstitutions substitution g
      }
    annotate
      seq@(UnclausifiedSequent fs is ucs g)
      (ClausificationNode (RightCs f projs) _) = do
      fTerm <- getTermFromEnvironment f
      let projsCount = length projs
      projsCaptureTerms <- zip [1..] <$> replicateM projsCount getNewTermFromEnvironment
      let projTerms = map (\(i, t) -> Abstraction [varName t] $ Application [Proj i, Application [fTerm, t]]) projsCaptureTerms
      let substitution = zip (map (varName . (ucs !)) projs) projTerms
      return seq {
        unclausified = Map.insert f fTerm (foldr Map.delete ucs projs),
        goal = applyLocalGoalSubstitutions substitution g
      }
    annotate
      seq@(UnclausifiedSequent fs is ucs g)
      (ClausificationNode (RightImpl fF gF) _) = do
      captureTerm <- getNewTermFromEnvironment
      fFTerm <- getTermFromEnvironment fF
      let gFTerm = ucs ! gF

      let substitution = Abstraction [varName captureTerm] $
            Application [fFTerm, Application [Proj 1, captureTerm], Application [Proj 2, captureTerm]]

      return seq {
        unclausified = Map.insert fF fFTerm $ Map.delete gF ucs,
        goal = applyLocalGoalSubstitution (varName gFTerm) substitution g
      }
    annotate
      seq@(UnclausifiedSequent fs is ucs g)
      (ClausificationNode (Aliasing f f' as) _) = do
      fTerm <- getTermFromEnvironment f
      let f'Term = ucs ! f'
      let asTerms = map (ucs !) as
      let substitutions = (varName f'Term, fTerm) : map ((, Id) . varName ) asTerms

      return seq {
        unclausified = Map.insert f fTerm (foldr Map.delete ucs (f':as)),
        goal = applyLocalGoalSubstitutions substitutions g
      }
    annotate
      seq@(UnclausifiedSequent fs is ucs g)
      (ClausificationNode (AsFlat f c) _) = do
      let f'Term = fs ! c
      fTerm <- getNewTermFromEnvironment
      substitution <- case f of 
                 (Atom _) -> do 
                    capture <- getNewTermFromEnvironment
                    return $
                      Abstraction [varName capture] $ Application [Sum 1, fTerm]
                 (Implication [Atom _, Atom _]) -> do
                    capture <- getNewTermFromEnvironment
                    return $
                      Abstraction [varName capture] $ 
                        Application [Sum 1,
                          Application [fTerm, Application [Proj 1, capture]]]
                 (Implication [Atom _, Disjunction ds]) -> do
                    capture <- getNewTermFromEnvironment
                    return $
                      Abstraction [varName capture] $
                        Application [fTerm, Application [Proj 1, capture]]
                 (Implication [Conjunction cs, Atom _]) -> do
                    capture <- getNewTermFromEnvironment
                    return $ 
                      Abstraction [varName capture] $
                        Application [Sum 1, Application [fTerm, capture]]
                 (Implication [Conjunction cs, Disjunction ds]) -> do
                    return fTerm
                 _ -> error "Wrong impl clause shit"

      return seq {
        flats = Map.delete c fs,
        unclausified = Map.insert f fTerm ucs,
        goal = applyLocalGoalSubstitution (varName f'Term) substitution g
      }
    annotate
      seq@(UnclausifiedSequent fs is ucs g)
      (ClausificationNode (AsImpl i) _) = do
      let iTerm = is ! i
      return seq {
        impls = Map.delete i is,
        unclausified = Map.insert (plain i) iTerm ucs,
        goal = goalPreserveTerm g
      }
    annotate 
      seq@(IntuitSequent fs is g)
      (ClausificationNode AsIntuit _) = do
      return UnclausifiedSequent {
        flats = fs,
        impls = is,
        unclausified = Map.empty,
        goal = goalPreserveTerm g
      }
    annotate 
      seq@(IntuitSequent fs is g)
      (ClausificationNode (ImplImpliesFlat impl flat) (IntuitPlainSequent pfs pis pg)) = do
      let flatTerm = fs ! flat
      let implTerm = is ! impl

      captureTerm <- getNewTermFromEnvironment

      let substitution = Abstraction [varName captureTerm] $
                           Application [Sum 1,
                             Application [implTerm,
                               Const $ Application [Proj 1, captureTerm]]]

      return IntuitSequent {
        flats = if flat `elem` pfs then fs else Map.delete flat fs,
        impls = is,
        goal = applyLocalGoalSubstitution (varName flatTerm) substitution g
      }

data CArrowRule = CPL0 | CPL1 (FlatClauseFormula Atom) (ImplClauseFormula Atom) 

data CArrowNode = CArrowNode {
  carrowRule :: CArrowRule,
  classicSequent :: PlainSequent,
  implSequent :: PlainSequent
}

annotateCArrowNodes :: [CArrowNode] -> State Environment [(Sequent, AnnotatedLJTNode)]
annotateCArrowNodes (cpl0@(CArrowNode CPL0 cseq iseq):cpl1s) = do
  (annotatedX, annotatedC) <- annotateCPL0 cpl0
  otherAnnotated <- annotate annotatedX cpl1s
  return ((annotatedX, annotatedC) : otherAnnotated)
  where
    annotateCPL0 :: CArrowNode -> State Environment (Sequent, AnnotatedLJTNode)
    annotateCPL0 (CArrowNode CPL0 cseq iseq@(IntuitPlainSequent _ impls _)) = do
      let provedCseq = proveLJT cseq
      annotatedClassic <- annotateLJTNode provedCseq
      let (ClassicSequent flats assumptions goal) = rootLJT annotatedClassic
  
      implAnnotations <- mapM getTermFromEnvironment impls

      return (IntuitSequent {
        flats = flats,
        impls = Map.fromList $ zip impls implAnnotations,
        goal = goal
      }, annotatedClassic)


    annotateCPL1 :: Sequent -> CArrowNode -> State Environment (Sequent, AnnotatedLJTNode)
    annotateCPL1 
      seq@(IntuitSequent flats' impls g)
      (CArrowNode (CPL1 phi lambda@(ImplClauseFormula a _ _)) cseq iseq) = do
      let provedCseq = proveLJT cseq
      annotatedClassic <- annotateLJTNode provedCseq
      let (ClassicSequent flats assumptions b) = rootLJT annotatedClassic

      let otherAssumptions = conjunctFormulas phi
      let otherAssumptionTerms = map (assumptions !) otherAssumptions

      let bTerm = goalTermOf b
      let aTerm = assumptions ! a

      bCapture <- getNewTermFromEnvironment
      let projSubstitutionTerms = aTerm : otherAssumptionTerms
      let enumeratedProjSubstitutionTerms = zip [1..] projSubstitutionTerms
      let projSubstitutions = map (\(i, t) -> (varName t, Application [Proj i, bCapture])) enumeratedProjSubstitutionTerms

      let csTerm = Abstraction
            [varName bCapture]  -- getting term names for a0...an
            (foldr (uncurry substitute) bTerm projSubstitutions)               -- getting b as body
  
      let lambdaTerm = impls ! lambda

      outerCapture <- getNewTermFromEnvironment
      innerCapture <- getNewTermFromEnvironment

      let phiSubstitution =
            Abstraction [varName outerCapture] $
            Application [
              Sum 1,
              Application [
                lambdaTerm,
                Abstraction [varName innerCapture] $
                  Application [csTerm, Application[Insert 1, outerCapture, innerCapture]]]
            ]
  
      let annotatedRoot = IntuitSequent {
            flats = flats,
            impls = impls,
            goal = applyLocalGoalSubstitution (varName $ flats' ! phi) phiSubstitution g
          }
  
      return (annotatedRoot, annotatedClassic)

    annotate :: Sequent -> [CArrowNode] -> State Environment [(Sequent, AnnotatedLJTNode)]
    annotate seq [] = return []
    annotate seq (h:t) = do
      (annotatedX, annotatedC) <- annotateCPL1 seq h
      othersAnnotated <- annotate annotatedX t

      return ((annotatedX, annotatedC) : othersAnnotated)
