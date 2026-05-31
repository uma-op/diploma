module ClassicSeqProver(module ClassicSeqProver) where

import qualified Data.List as List
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Control.Monad.State
import Sequent
import Clause
import Formula
import Term

data LJTNode =
  Axiom PlainSequent |
  Cs PlainSequent LJTNode (FlatClauseFormula Atom, FlatClauseFormula Atom, Atom) |
  Ds PlainSequent [LJTNode] (FlatClauseFormula Atom)

instance Show LJTNode where
  show (Axiom pseq) = "Ax: [" ++ plainSequentToString pseq  ++ "]"
  show (Cs pseq dt _) = "Cs: [" ++ plainSequentToString pseq ++ "] {" ++ show dt ++ "}"
  show (Ds pseq dts _) = "Ds: [" ++ plainSequentToString pseq ++ "] {" ++ List.intercalate ", " (map show dts) ++ "}"

proveLJT :: PlainSequent -> LJTNode
proveLJT pseq@ClassicPlainSequent{} =
  case applyAxiom pseq of
    Just () -> Axiom pseq
    Nothing ->
      case applyCs pseq of
        Just (newPseq, keyF, newF, atom) -> Cs pseq (proveLJT newPseq) (keyF, newF, atom)
        Nothing -> 
          case applyDs pseq of
            Just (newPseqs, keyF) -> Ds pseq (map proveLJT newPseqs) keyF
            Nothing -> error "Wrong sequen"
  where
    applyAxiom :: PlainSequent -> Maybe ()
    applyAxiom pseq@(ClassicPlainSequent r a g) =
      if g `elem` a
        then Just ()
        else Nothing
    applyAxiom _ = undefined

    applyCs :: PlainSequent -> Maybe (PlainSequent, FlatClauseFormula Atom, FlatClauseFormula Atom, Atom)
    applyCs pseq@(ClassicPlainSequent r a g) = do
      (atom, flat@(FlatClauseFormula cs ds)) <- maybeFoundCs
      let newClause = FlatClauseFormula (List.delete atom cs) ds
      return
        (ClassicPlainSequent
          (newClause : List.delete flat r) a g,
          flat,
          newClause,
          atom)
      where
        maybeFoundCs = List.find (uncurry csPred) [(a', r') | a' <- a, r' <- r]
        csPred atom (FlatClauseFormula cs _) = atom `elem` cs
    applyCs _ = undefined

    applyDs :: PlainSequent -> Maybe ([PlainSequent], FlatClauseFormula Atom)
    applyDs pseq@(ClassicPlainSequent r a g) = do
      found@(FlatClauseFormula _ ds) <- maybeFoundDs
      let newSeqBase = ClassicPlainSequent (List.delete found r) a g
      return ([newSeqBase { plainAssumptions = d : a } | d <- ds], found)
      where
        maybeFoundDs = List.find dsPred r
        dsPred (FlatClauseFormula [] _) = True
        dsPred _ = False
    applyDs _ = undefined

proveLJT _ = error "RSeq should be classic form"

annotateLJTNode :: LJTNode -> State Environment Sequent 
annotateLJTNode node@(Axiom (ClassicPlainSequent r a g)) = do
  rTerms <- mapM getTermFromEnvironment r
  aTerms <- mapM getTermFromEnvironment a
  gTerm <- getTermFromEnvironment g
  return ClassicSequent {
    flats = Map.fromList (zip r rTerms),
    assumptions = Map.fromList (zip a aTerms),
    goal = Map.singleton g gTerm
  }
annotateLJTNode node@(Cs (ClassicPlainSequent r a g) dt (keyClause, newClause, a0)) = do
  annotated <- annotateLJTNode dt
  let (ClassicSequent r' a' g') = annotated
  keyClauseTerm <- getNewTermFromEnvironment
  let newClauseTerm = r' ! newClause
  let a0Term = a' ! a0
  let (goalFormula, goalTerm) = Map.findMin g'
  captureTerm <- getNewTermFromEnvironment

  let substitution = Abstraction [varName captureTerm] $ Application [keyClauseTerm, Application [
        Insert (length $ conjunctFormulas newClause) 1, captureTerm, a0Term]]
  return ClassicSequent {
    flats = Map.insert keyClause keyClauseTerm $ Map.delete newClause r',
    assumptions = a',
    goal = Map.singleton goalFormula (substitute (varName newClauseTerm) substitution goalTerm)
  }
annotateLJTNode node@(Ds (ClassicPlainSequent r a g) dts f@(FlatClauseFormula [] ds)) = do
  annotated <- mapM annotateLJTNode dts
  fTerm <- getNewTermFromEnvironment

  return ClassicSequent {
    flats = Map.insert f fTerm $ flats (head annotated),  -- get first sequent flats then add new disjunction
    assumptions = Map.delete (head ds) $ assumptions (head annotated), -- get first sequent assumptions then remove first of ds
    goal = Map.singleton g $ Case fTerm [(aas ! d, head (Map.elems ag)) | (d, ClassicSequent _ aas ag) <- zip ds annotated]   -- case f [ds[0] ag0, ..., case ds[n] agn]
  }

annotateLJTNode _ = error "Wrong"
