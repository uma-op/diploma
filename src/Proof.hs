{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-binds #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Proof where

import Data.Void
import Data.Map(Map, (!))
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Control.Monad.State
import qualified Data.List as List
import Control.Monad

import Formula(Formula(..), PlainFormula, Atom, plainFormulaToString, atom)
import qualified Formula
import Clause (FlatClauseFormula, ImplClauseFormula(..))
import qualified Clause
import qualified Clause as Formula

data Term =
  Abstraction [String] Term |
  Application [Term] |
  Variable { varName :: String } |
  Id |
  GetSum Int Int |
  GetProduct Int Int |
  Const Term

substitute ::  -- substitute term without unification
  String ->  -- term(variable) name
  Term ->  -- term to substitute
  Term ->  -- the term in which is substituted
  Term
substitute name arg (Abstraction capture body) = Abstraction capture $ substitute name arg body
substitute name arg (Application terms) = Application $ map (substitute name arg) terms
substitute name arg var@(Variable termName) = if name == termName then arg else var

type Annotated f = Map f Term

data Environment = Environment {
  cache :: Map PlainFormula Term,
  vcount :: Int
}

newEnvironment :: Environment
newEnvironment = Environment {
  cache = Map.empty,
  vcount = 0
}

getTermFromEnvironment :: Formula a => a -> State Environment Term
getTermFromEnvironment formula = state newState
  where
    plainFormula = Formula.plain formula
    newState :: Environment -> (Term, Environment)
    newState env@(Environment cache vcount) = case Map.lookup plainFormula cache of
      Just term -> (term, env)
      Nothing -> (newTerm, env { cache = newCache, vcount = newVCount })
      where
        newTerm = Variable $ "$" ++ show vcount
        newVCount = vcount + 1
        newCache = Map.insert plainFormula newTerm cache


getNewTermFromEnvironment :: State Environment Term
getNewTermFromEnvironment = state newState
  where
    newState :: Environment -> (Term, Environment)
    newState env@(Environment _ vcount) = (Variable $ "$" ++ show vcount, env { vcount = vcount + 1 })

data PlainSequent = ClassicPlainSequent {
  plainFlats :: [FlatClauseFormula Atom],
  plainAssumptions :: [Atom],
  plainGoal :: Atom
} | IntuitPlainSequent {
  plainFlats :: [FlatClauseFormula Atom],
  plainImpls :: [ImplClauseFormula Atom],
  plainGoal :: Atom
} | UnclausifiedPlainSequent {
  plainFlats :: [FlatClauseFormula Atom],
  plainImpls :: [ImplClauseFormula Atom],
  plainUnclausified :: [PlainFormula],
  plainGoal :: Atom
}

data Sequent =
  ClassicSequent {
    flats :: Annotated (FlatClauseFormula Atom),
    assumptions :: Annotated Atom,
    goal :: Annotated Atom
  } |
  IntuitSequent {
    flats :: Annotated (FlatClauseFormula Atom),
    impls :: Annotated (ImplClauseFormula Atom),
    goal :: Annotated Atom
  } |
  UnclausifiedSequent {
    flats :: Annotated (FlatClauseFormula Atom),
    impls :: Annotated (ImplClauseFormula Atom),
    unclausified :: Annotated PlainFormula,
    goal :: Annotated Atom
  }

type ClassicProof = Void 

data ClausificationRule =
  MakeImpl PlainFormula PlainFormula |
  LeftDs PlainFormula [PlainFormula] |
  RightCs PlainFormula [PlainFormula] |
  RightImpl PlainFormula PlainFormula PlainFormula |
  Aliasing PlainFormula PlainFormula [PlainFormula] |

  AsFlat PlainFormula |
  AsImpl PlainFormula |
  AsIntuit

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
      let varTerms = map (\(i, t) -> Abstraction [varName t] $ Application [fTerm, Application [GetSum varsCount i]]) varCaptureTerms
      let substitution = zip (map show vars) varTerms
      let (gFormula, gTerm) = Map.findMin g
      return seq {
        unclausified = Map.insert f fTerm (foldr Map.delete ucs vars),
        goal = Map.singleton gFormula (substitute gTerm)
      }

data CArrowRule = CPL0 | CPL1 (FlatClauseFormula Atom) (ImplClauseFormula Atom) 

data CArrowNode = CArrowNode {
  carrowRule :: CArrowRule,
  classicSequent :: Sequent,
  implSequent :: Sequent
}

data ClassicDerivationTree = ClassicDerivationTree {
  proof :: ClassicProof,
  rootCDT :: Sequent
}

-- data CArrowDerivationTree =
--   CPL0 {
--     classicBranch :: ClassicDerivationTree,
--     rootCADT :: Sequent  -- intuit sequent
--   } |
--   CPL1 {
--     classicBranch :: ClassicDerivationTree,
--     carrowBranch :: CArrowDerivationTree,
--     rootCADT :: Sequent,
-- 
--     learnedImplClause :: ImplClauseFormula Atom,
--     addedFlatClause :: FlatClauseFormula Atom
--   }
--     
-- class DerivationTree dt where
--   root :: dt -> Sequent
--   annotate :: dt -> State Environment dt
-- 
-- instance DerivationTree ClassicDerivationTree where
--   root = rootCDT
--   annotate = undefined
-- 
-- instance DerivationTree CArrowDerivationTree where
--   root = rootCADT
-- 
--   annotate cpl1@(
--     CPL1
--       classicBranch
--       carrowBranch
--       cpl1root
--       lambda@(ImplClauseFormula a _ _)
--       phi
--     ) = do
-- 
--     annotatedClassicBranch <- annotate classicBranch
--     let annotatedClassicBranchRoot@(
--             ClassicSequent flats assumptions b
--           ) = root annotatedClassicBranch
--     annotatedCArrowBranch <- annotate carrowBranch
--     let annotatedCArrowBranchRoot@(
--             IntuitSequent 
--               flats' impls goal
--           ) = root annotatedCArrowBranch
-- 
--     let aTerm = assumptions ! a
--     let outerCapture = Map.elems $ Map.delete a assumptions
-- 
--     let csTerm = Abstraction
--           (map varName (aTerm:outerCapture))  -- getting term names for a0...an
--           (snd $ Map.findMin b)               -- getting b as body
-- 
--     let lambdaTerm = impls ! lambda
--     
--     innerCapture <- getNewTermFromEnvironment
--     let phiSubstitution =
--           Abstraction (map varName outerCapture) $
--           Application [
--             lambdaTerm,
--             Abstraction [varName innerCapture] $
--             Application ([csTerm, innerCapture] ++ outerCapture)
--           ]
-- 
--     let (goalFormula, goalTerm) = Map.findMin goal
--     let annotatedRoot = IntuitSequent {
--           flats = flats,
--           impls = impls,
--           goal = Map.singleton goalFormula $ substitute (varName $ flats' ! phi) phiSubstitution goalTerm
--         }
-- 
--     return $ cpl1 {
--       classicBranch = annotatedClassicBranch,
--       carrowBranch = annotatedCArrowBranch,
--       rootCADT = annotatedRoot
--     }
-- 
--   annotate cpl0@(
--     CPL0
--       classicBranch
--       rootCADT@(IntuitSequent _ impls _)
--     ) = do
--     annotatedClassicBranch <- annotate classicBranch
--     let annotatedClassicBranchRoot@(
--           ClassicSequent
--             flats assumptions goal) = root annotatedClassicBranch
-- 
--     let capture = Map.elems assumptions
--     let (goalFormula, goalTerm) = Map.findMin goal
--     let csTerm = Abstraction (map varName capture) goalTerm
-- 
--     annotatedImpls <- sequence $ Map.fromSet getTermFromEnvironment (Map.keysSet impls)
--     let annotatedRoot = IntuitSequent {
--       flats = flats,
--       impls = annotatedImpls,
--       goal = Map.singleton goalFormula csTerm
--     }
-- 
--     return cpl0
-- 

plainSequentToString :: PlainSequent -> String
plainSequentToString (ClassicPlainSequent fs as g) =
  "R: " ++ List.intercalate ", " flatStrings ++
  " A: " ++ List.intercalate ", " assumptionStrings ++
  " |- " ++ goalString
  where
    flatStrings = map (plainFormulaToString . plain) fs 
    assumptionStrings = map (plainFormulaToString . plain) as 
    goalString = (plainFormulaToString . plain) g
plainSequentToString (IntuitPlainSequent fs is g) =
  "R: " ++ List.intercalate ", " flatStrings ++
  " X: " ++ List.intercalate ", " implStrings ++
  " |- " ++ goalString
  where
    flatStrings = map (plainFormulaToString . plain) fs 
    implStrings = map (plainFormulaToString . plain) is 
    goalString = (plainFormulaToString . plain) g
plainSequentToString (UnclausifiedPlainSequent fs is uc g) =
  "R: {" ++ List.intercalate ", " flatStrings ++
  "} X: {" ++ List.intercalate ", " implStrings ++
  "} U: {" ++ List.intercalate ", " unclausifiedStrings ++
  "} |- " ++ goalString
  where
    flatStrings = map (plainFormulaToString . plain) fs 
    implStrings = map (plainFormulaToString . plain) is 
    unclausifiedStrings = map plainFormulaToString uc
    goalString = (plainFormulaToString . plain) g

