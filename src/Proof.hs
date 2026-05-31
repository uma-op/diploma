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

  AsFlat (FlatClauseFormula Atom) |
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

data ClausificationNode = ClausificationNode {
  clausificationRule :: ClausificationRule,
  unclausifiedSequent :: PlainSequent
}

annotateClausificationNodes :: Sequent -> [ClausificationNode] -> State Environment Sequent
annotateClausificationNodes seq [] = return seq
annotateClausificationNodes seq (h:t) = do 
  annotated <- annotate seq h
  annotateClausificationNodes annotated t
  where
    annotate :: Sequent -> ClausificationNode -> State Environment Sequent
    annotate
      seq@(UnclausifiedSequent fs is ucs g)
      (ClausificationNode (MakeImpl x f) _) = do
      xTerm <- getTermFromEnvironment x
      let (gFormula, gTerm) = Map.findMin g
      return seq {
        unclausified = Map.insert x xTerm $ Map.delete f ucs,
        goal = Map.singleton gFormula $ substitute (varName (ucs ! f)) (Const xTerm) gTerm
      }
    annotate  
      seq@(UnclausifiedSequent fs is ucs g)
      (ClausificationNode (LeftDs f vars) _) = do
      fTerm <- getNewTermFromEnvironment
      let varsCount = length vars 
      varCaptureTerms <- zip [0..] <$> replicateM varsCount getNewTermFromEnvironment
      let varTerms = map (\(i, t) -> Abstraction [varName t] $ Application [fTerm, Application [GetSum varsCount i, t]]) varCaptureTerms
      let substitution = zip (map plainFormulaToString vars) varTerms
      let (gFormula, gTerm) = Map.findMin g
      return seq {
        unclausified = Map.insert f fTerm (foldr Map.delete ucs vars),
        goal = Map.singleton gFormula (foldr (uncurry substitute) gTerm substitution)
      }
    annotate
      seq@(UnclausifiedSequent fs is ucs g)
      (ClausificationNode (RightCs f projs) _) = do
      fTerm <- getNewTermFromEnvironment
      let projsCount = length projs
      projsCaptureTerms <- zip [0..] <$> replicateM projsCount getNewTermFromEnvironment
      let projTerms = map (\(i, t) -> Abstraction [varName t] $ Application [GetProduct projsCount i, Application [fTerm, t]]) projsCaptureTerms
      let substitution = zip (map plainFormulaToString projs) projTerms
      let (gFormula, gTerm) = Map.findMin g
      return seq {
        unclausified = Map.insert f fTerm (foldr Map.delete ucs projs),
        goal = Map.singleton gFormula (foldr (uncurry substitute) gTerm substitution)
      }
    annotate
      seq@(UnclausifiedSequent fs is ucs g)
      (ClausificationNode (RightImpl fF gF) _) = do
      captureTerm <- getNewTermFromEnvironment
      fFTerm <- getNewTermFromEnvironment
      let gFTerm = ucs ! gF
      let (gFormula, gTerm) = Map.findMin g

      let substitution = Abstraction [varName captureTerm] $
            Application [fFTerm, Application [GetProduct 2 0, captureTerm], Application [GetProduct 2 1, captureTerm]]

      return seq {
        unclausified = Map.insert fF fFTerm $ Map.delete gF ucs,
        goal = Map.singleton gFormula $ substitute (varName gFTerm) substitution gTerm
      }
    annotate
      seq@(UnclausifiedSequent fs is ucs g)
      (ClausificationNode (Aliasing f f' as) _) = do
      fTerm <- getNewTermFromEnvironment
      let f'Term = ucs ! f'
      let asTerms = map (ucs !) as
      let (gFormula, gTerm) = Map.findMin g

      let substitutions = (varName f'Term, fTerm) : map ((, Id) . varName ) asTerms

      return seq {
        unclausified = Map.insert f fTerm (foldr Map.delete ucs (f':as)),
        goal = Map.singleton gFormula (foldr (uncurry substitute) gTerm substitutions)
      }
    annotate
      seq@(UnclausifiedSequent fs is ucs g)
      (ClausificationNode (AsFlat f) _) = do
      let fTerm = fs ! f
      return seq {
        flats = Map.delete f fs,
        unclausified = Map.insert (plain f) fTerm ucs
      }
    annotate
      seq@(UnclausifiedSequent fs is ucs g)
      (ClausificationNode (AsImpl i) _) = do
      let iTerm = is ! i
      return seq {
        impls = Map.delete i is,
        unclausified = Map.insert (plain i) iTerm ucs
      }
    annotate 
      seq@(IntuitSequent fs is g)
      (ClausificationNode AsIntuit _) = do
      return UnclausifiedSequent {
        flats = fs,
        impls = is,
        unclausified = Map.empty,
        goal = g
      }

data CArrowRule = CPL0 | CPL1 (FlatClauseFormula Atom) (ImplClauseFormula Atom) 

data CArrowNode = CArrowNode {
  carrowRule :: CArrowRule,
  classicSequent :: PlainSequent,
  implSequent :: PlainSequent
}

annotateCArrowNodes :: [CArrowNode] -> State Environment Sequent
annotateCArrowNodes (cpl0@(CArrowNode CPL0 cseq iseq):cpl1s) = do
  annotated <- annotateCPL0 cpl0
  annotate annotated cpl1s
  where
    annotateCPL0 :: CArrowNode -> State Environment Sequent
    annotateCPL0 (CArrowNode CPL0 cseq iseq@(IntuitPlainSequent _ impls _)) = do
      let provedCseq = proveLJT cseq
      annotatedClassic <- annotateLJTNode provedCseq
      let (ClassicSequent flats assumptions goal) = annotatedClassic
  
      let capture = Map.elems assumptions
      let (goalFormula, goalTerm) = Map.findMin goal
      let csTerm = Abstraction (map varName capture) goalTerm
  
      implAnnotations <- mapM getTermFromEnvironment impls

      return IntuitSequent {
        flats = flats,
        impls = Map.fromList $ zip impls implAnnotations,
        goal = Map.singleton goalFormula csTerm
      }


    annotateCPL1 :: Sequent -> CArrowNode -> State Environment Sequent
    annotateCPL1 
      seq@(IntuitSequent flats' impls g)
      (CArrowNode (CPL1 phi lambda@(ImplClauseFormula a _ _)) cseq iseq) = do
      let provedCseq = proveLJT cseq
      annotatedClassic  <- annotateLJTNode provedCseq
      let (ClassicSequent flats assumptions b) = annotatedClassic

      let aTerm = assumptions ! a
      let outerCapture = Map.elems $ Map.delete a assumptions
  
      let csTerm = Abstraction
            (map varName (aTerm:outerCapture))  -- getting term names for a0...an
            (snd $ Map.findMin b)               -- getting b as body
  
      let lambdaTerm = impls ! lambda
      
      innerCapture <- getNewTermFromEnvironment
      let phiSubstitution =
            Abstraction (map varName outerCapture) $
            Application [
              lambdaTerm,
              Abstraction [varName innerCapture] $
              Application ([csTerm, innerCapture] ++ outerCapture)
            ]
  
      let (goalFormula, goalTerm) = Map.findMin g
      let annotatedRoot = IntuitSequent {
            flats = flats,
            impls = impls,
            goal = Map.singleton goalFormula $ substitute (varName $ flats' ! phi) phiSubstitution goalTerm
          }
  
      return annotatedRoot

    annotate :: Sequent -> [CArrowNode] -> State Environment Sequent
    annotate seq [] = return seq
    annotate seq (h:t) = do
      annotated <- annotateCPL1 seq h
      annotate annotated t
