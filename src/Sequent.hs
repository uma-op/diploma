module Sequent where

import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State
import qualified Data.List as List

import Clause
import Formula
import Term

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
        newTerm = Var $ "$" ++ show vcount
        newVCount = vcount + 1
        newCache = Map.insert plainFormula newTerm cache


getNewTermFromEnvironment :: State Environment Term
getNewTermFromEnvironment = state newState
  where
    newState :: Environment -> (Term, Environment)
    newState env@(Environment _ vcount) = (Var $ "$" ++ show vcount, env { vcount = vcount + 1 })


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

sequentToString :: Sequent -> String
sequentToString (ClassicSequent fs as g) =
  "R: " ++ List.intercalate ", " flatStrings ++
  " A: " ++ List.intercalate ", " assumptionStrings ++
  " |- " ++ goalString
  where 
    flatStrings = map (\(c, t) -> formulaToString c ++ " ~ " ++ show t) $ Map.toList fs
    assumptionStrings = map (\(a, t) -> formulaToString a ++ " ~ " ++ show t) $ Map.toList as
    (goalFormula, goalTerm) = Map.findMin g
    goalString = formulaToString goalFormula ++ " ~ " ++ show goalTerm 
sequentToString _ = error "Not implemented"
-- sequentToString (ClassicSequent fs as g) =
--   "R: " ++ List.intercalate ", " flatStrings ++
--   " A: " ++ List.intercalate ", " assumptionStrings ++
--   " |- " ++ goalString
--   where 
--     flatStrings = map (\(c, t) -> formulaToString c ++ " ~ " ++ show t) $ Map.toList fs
--     assumptionStrings = map (\(a, t) -> formulaToString a ++ " ~ " ++ show t) $ Map.toList as
--     (goalFormula, goalTerm) = Map.findMin g
--     goalString = formulaToString goalFormula ++ " ~ " ++ show goalTerm 
-- sequentToString (ClassicSequent fs as g) =
--   "R: " ++ List.intercalate ", " flatStrings ++
--   " A: " ++ List.intercalate ", " assumptionStrings ++
--   " |- " ++ goalString
--   where 
--     flatStrings = map (\(c, t) -> formulaToString c ++ " ~ " ++ show t) $ Map.toList fs
--     assumptionStrings = map (\(a, t) -> formulaToString a ++ " ~ " ++ show t) $ Map.toList as
--     (goalFormula, goalTerm) = Map.findMin g
--     goalString = formulaToString goalFormula ++ " ~ " ++ show goalTerm 


plainSequentToString :: PlainSequent -> String
plainSequentToString (ClassicPlainSequent fs as g) =
  "R: " ++ List.intercalate ", " flatStrings ++
  " A: " ++ List.intercalate ", " assumptionStrings ++
  " |- " ++ goalString
  where
    flatStrings = map (plainFormulaToString . plain) fs 
    assumptionStrings = map formulaToString as 
    goalString = formulaToString g
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

