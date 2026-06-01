module ClassicSeqProver(module ClassicSeqProver) where

import qualified Data.List as List
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Control.Monad.State
import Sequent
import Clause
import Formula
import Term
import Debug.Trace

data LJTNode =
  Axiom PlainSequent |
  Cs PlainSequent LJTNode (FlatClauseFormula Atom, FlatClauseFormula Atom, Atom) |
  Ds PlainSequent [LJTNode] (FlatClauseFormula Atom)

instance Show LJTNode where
  show (Axiom pseq) = "Ax: [" ++ plainSequentToString pseq  ++ "]"
  show (Cs pseq dt _) = "Cs: [" ++ plainSequentToString pseq ++ "] {" ++ show dt ++ "}"
  show (Ds pseq dts _) = "Ds: [" ++ plainSequentToString pseq ++ "] {" ++ List.intercalate ", " (map show dts) ++ "}"

data AnnotatedLJTNode =
  AnnotatedAxiom {
    rootLJT :: Sequent
  } |
  AnnotatedCs {
    rootLJT :: Sequent,
    branchLJT :: AnnotatedLJTNode,
    csRuleContext :: (FlatClauseFormula Atom, FlatClauseFormula Atom, Atom)
  } |
  AnnotatedDs {
    rootLJT :: Sequent,
    branchesLJT :: [AnnotatedLJTNode],
    dsRuleContext :: FlatClauseFormula Atom
  }

instance Show AnnotatedLJTNode where
  show (AnnotatedAxiom root) = "Ax: [" ++ sequentToString root ++ "]"
  show (AnnotatedCs root dt _) = "Cs: [" ++ sequentToString root ++ "] {" ++ show dt ++ "}"
  show (AnnotatedDs root dts _) = "Ds: [" ++ sequentToString root ++ "] {" ++ List.intercalate ", " (map show dts) ++ "}"

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
            Nothing -> error "Wrong sequent"
  where
    applyAxiom :: PlainSequent -> Maybe ()
    applyAxiom pseq@(ClassicPlainSequent r a g) =
      if g `elem` a
        then Just ()
        else Nothing
    applyAxiom _ = undefined

    applyCs :: PlainSequent -> Maybe (PlainSequent, FlatClauseFormula Atom, FlatClauseFormula Atom, Atom)
    applyCs pseq@(ClassicPlainSequent r a g) = do
      (atom, flat@(FlatClauseFormula cs ds _)) <- maybeFoundCs
      let newClause = FlatClauseFormula (List.delete atom cs) ds
            (Implication [Conjunction (Atom <$> List.delete atom cs), Disjunction $ Atom <$> ds])
      return
        (ClassicPlainSequent
          (newClause : List.delete flat r) a g,
          flat,
          newClause,
          atom)
      where
        maybeFoundCs = List.find (uncurry csPred) [(a', r') | a' <- a, r' <- r]
        csPred atom (FlatClauseFormula cs _ _) = atom `elem` cs
    applyCs _ = undefined

    applyDs :: PlainSequent -> Maybe ([PlainSequent], FlatClauseFormula Atom)
    applyDs pseq@(ClassicPlainSequent r a g) = do
      found@(FlatClauseFormula _ ds _) <- maybeFoundDs
      let newSeqBase = ClassicPlainSequent (List.delete found r) a g
      return ([newSeqBase { plainAssumptions = d : a } | d <- ds], found)
      where
        maybeFoundDs = List.find dsPred r
        dsPred (FlatClauseFormula [] _ _) = True
        dsPred _ = False
    applyDs _ = undefined

proveLJT _ = error "RSeq should be classic form"

annotateLJTNode :: LJTNode -> State Environment AnnotatedLJTNode 
annotateLJTNode node@(Axiom (ClassicPlainSequent r a g)) = do
  rTerms <- mapM getTermFromEnvironment r
  aTerms <- mapM getTermFromEnvironment a
  gTerm <- getTermFromEnvironment g

  return AnnotatedAxiom {
    rootLJT = ClassicSequent {
      flats = Map.fromList (zip r rTerms),
      assumptions = Map.fromList (zip a aTerms),
      goal = singletonGoal g gTerm
    }
  }

annotateLJTNode node@(Cs (ClassicPlainSequent r a g) dt ctx@(keyClause, newClause, a0)) = do
  annotated <- annotateLJTNode dt
  let (ClassicSequent r' a' g') = rootLJT annotated
  let (goalFormula, _) = Map.findMin g'
  keyClauseTerm <- getTermFromEnvironment keyClause
  let newClauseTerm = r' ! newClause
  let a0Term = a' ! a0
  captureTerm <- getNewTermFromEnvironment

  let substitution = Abstraction [varName captureTerm] $ Application [keyClauseTerm, Application [
        Insert 1, captureTerm, a0Term]]

  return AnnotatedCs {
    rootLJT = ClassicSequent {
      flats = Map.insert keyClause keyClauseTerm $ if newClause `elem` r then r' else Map.delete newClause r',
      assumptions = a',
      goal = goalApplyLocalSubstitution goalFormula (varName newClauseTerm) substitution (goalTermOf g')
    },
    branchLJT = annotated,
    csRuleContext = ctx
  }

annotateLJTNode node@(Ds (ClassicPlainSequent r a g) dts f@(FlatClauseFormula [] ds _)) = do
  annotated <- mapM annotateLJTNode dts
  let annotatedRoots = map rootLJT annotated 
  fTerm <- getTermFromEnvironment f

  return AnnotatedDs {
    rootLJT = ClassicSequent {
      flats = Map.insert f fTerm $ flats (head annotatedRoots),  -- get first sequent flats then add new disjunction
      assumptions =
        if head ds `elem` a
          then assumptions (head annotatedRoots)
          else Map.delete (head ds) $ assumptions (head annotatedRoots),
      goal = singletonGoal g $ Application [
        Case [(aas ! d, goalTermOf ag) | (d, ClassicSequent _ aas ag) <- zip ds annotatedRoots],
        Application [fTerm, Id]]
    },
    branchesLJT = annotated,
    dsRuleContext = f
  }

annotateLJTNode _ = error "Wrong"
