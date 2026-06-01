module Sequent where

import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State
import qualified Data.List as List

import Clause
import Formula
import Term

type Annotated f = Map f Term

data AnnotatedGoal = AnnotatedGoal {
  goalTerm :: Term,
  goalSubstitutions :: [(String, Term)]
}

type Goal = Map Atom AnnotatedGoal

singletonGoal :: Atom -> Term -> Goal
singletonGoal atom term = Map.singleton atom (AnnotatedGoal term [])

goalApplyLocalSubstitution :: Atom -> String -> Term -> Term -> Goal
goalApplyLocalSubstitution atom name arg term =
  Map.singleton atom $ AnnotatedGoal (substitute name arg term) [(name, arg)]

goalApplyLocalSubstitutions :: Atom -> [(String, Term)] -> Term -> Goal
goalApplyLocalSubstitutions atom pairs term =
  Map.singleton atom $ AnnotatedGoal (foldr (uncurry substitute) term pairs) pairs

goalApplySubstitution :: String -> Term -> Goal -> Goal
goalApplySubstitution name arg goal =
  let (goalFormula, AnnotatedGoal term substitutions) = Map.findMin goal
  in Map.singleton goalFormula $
       AnnotatedGoal (substitute name arg term) (substitutions ++ [(name, arg)])

goalApplySubstitutions :: [(String, Term)] -> Goal -> Goal
goalApplySubstitutions pairs goal =
  let (goalFormula, AnnotatedGoal term substitutions) = Map.findMin goal
  in Map.singleton goalFormula $
       AnnotatedGoal (foldr (uncurry substitute) term pairs) (substitutions ++ pairs)

goalWithTerm :: Atom -> Term -> Goal -> Goal
goalWithTerm atom term goal =
  let substitutions = goalSubstitutions (snd (Map.findMin goal))
  in Map.singleton atom (AnnotatedGoal term substitutions)

goalTermOf :: Goal -> Term
goalTermOf goal = goalTerm (snd (Map.findMin goal))

goalPreserveTerm :: Goal -> Goal
goalPreserveTerm goal =
  let (atom, AnnotatedGoal term _) = Map.findMin goal
  in singletonGoal atom term

applyLocalGoalSubstitution :: String -> Term -> Goal -> Goal
applyLocalGoalSubstitution name arg goal =
  let (goalFormula, AnnotatedGoal term _) = Map.findMin goal
  in goalApplyLocalSubstitution goalFormula name arg term

applyLocalGoalSubstitutions :: [(String, Term)] -> Goal -> Goal
applyLocalGoalSubstitutions pairs goal =
  let (goalFormula, AnnotatedGoal term _) = Map.findMin goal
  in goalApplyLocalSubstitutions goalFormula pairs term

formatGoal :: Goal -> String
formatGoal goal =
  let (goalFormula, AnnotatedGoal term substitutions) = Map.findMin goal
      substitutionLines = map (\(name, arg) -> name ++ " / " ++ show arg) substitutions
  in formulaToString goalFormula ++ "\n" ++ show (reduce term)
     ++ if null substitutionLines then "" else "\n" ++ unlines substitutionLines

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
    goal :: Goal
  } |
  IntuitSequent {
    flats :: Annotated (FlatClauseFormula Atom),
    impls :: Annotated (ImplClauseFormula Atom),
    goal :: Goal
  } |
  UnclausifiedSequent {
    flats :: Annotated (FlatClauseFormula Atom),
    impls :: Annotated (ImplClauseFormula Atom),
    unclausified :: Annotated PlainFormula,
    goal :: Goal
  }

sequentToString :: Sequent -> String
sequentToString (ClassicSequent fs as g) =
  "R:\n" ++ unlines flatStrings ++
  "A:\n" ++ unlines assumptionStrings ++
  " |-\n" ++ formatGoal g
  where 
    flatStrings = map (\(c, t) -> formulaToString c ++ " ~ " ++ show t) $ Map.toList fs
    assumptionStrings = map (\(a, t) -> formulaToString a ++ " ~ " ++ show t) $ Map.toList as
sequentToString (UnclausifiedSequent fs is ucs g) =
  "R:\n" ++ unlines flatStrings ++
  "X:\n" ++ unlines implStrings ++
  "U:\n" ++ unlines unclausifiedStrings ++
  " |-\n" ++ formatGoal g
  where
    flatStrings = map (\(c, t) -> formulaToString c ++ " ~ " ++ show t) $ Map.toList fs
    implStrings = map (\(c, t) -> formulaToString c ++ " ~ " ++ show t) $ Map.toList is
    unclausifiedStrings = map (\(c, t) -> formulaToString c ++ " ~ " ++ show t) $ Map.toList ucs
sequentToString (IntuitSequent fs is g) =
  "R:\n" ++ unlines flatStrings ++
  "X:\n" ++ unlines implStrings ++
  " |-\n" ++ formatGoal g
  where
    flatStrings = map (\(c, t) -> formulaToString c ++ " ~ " ++ show t) $ Map.toList fs
    implStrings = map (\(c, t) -> formulaToString c ++ " ~ " ++ show t) $ Map.toList is

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
  "R:\n" ++ unlines flatStrings ++
  "A:\n" ++ unlines assumptionStrings ++
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

reduceGoal :: Sequent -> Sequent
reduceGoal seq =
  let (goalFormula, AnnotatedGoal term substitutions) = Map.findMin (goal seq)
  in seq {
    goal = Map.singleton goalFormula (AnnotatedGoal (reduce term) substitutions)
  }
