module Formula where

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map, (!))
import qualified Data.List as List

import qualified Z3.Monad as Z3

data Formula = Implication [Formula]
             | Conjunction [Formula]
             | Disjunction [Formula]
             | Negation Formula
             | Variable String
             | Bottom
             deriving (Eq)

instance Show Formula where
  show Bottom = "_|_"
  show (Variable name) = name
  show (Negation f) = "-" ++ show f
  show (Disjunction ds) = "(" ++ List.intercalate " \\/ " (map show ds) ++ ")"
  show (Conjunction cs) = "(" ++ List.intercalate " /\\ " (map show cs) ++ ")"
  show (Implication is) = "(" ++ List.intercalate " -> " (map show is) ++ ")"

instance Ord Formula where
  compare Bottom Bottom = EQ
  compare Bottom _ = LT
  compare _ Bottom = GT
  compare (Variable x) (Variable y) = compare x y
  compare (Variable _) _ = LT
  compare _ (Variable _) = GT
  compare (Negation x) (Negation y) = compare x y
  compare (Negation _) _ = LT
  compare _ (Negation _) = GT
  compare (Conjunction xs) (Conjunction ys) = compare xs ys
  compare (Conjunction _) _ = LT
  compare _ (Conjunction _) = GT
  compare (Disjunction xs) (Disjunction ys) = compare xs ys
  compare (Disjunction _) _ = LT
  compare _ (Disjunction _) = GT
  compare (Implication xs) (Implication ys) = compare xs ys

variables :: Formula -> Set String
variables (Implication fs) = foldMap variables fs
variables (Conjunction fs) = foldMap variables fs
variables (Disjunction fs) = foldMap variables fs
variables (Negation fs) = variables fs
variables (Variable vname) = Set.singleton vname
variables Bottom = Set.singleton "_|_"

implication :: Formula -> Formula -> Formula
implication lhs rhs@(Implication impls) = Implication (lhs:impls)
implication lhs rhs = Implication [lhs, rhs]

conjunction :: Formula -> Formula -> Formula
conjunction lhs@(Conjunction lcs) rhs@(Conjunction rcs) = Conjunction (lcs ++ rcs)
conjunction lhs@(Conjunction lcs) rhs = Conjunction (rhs:lcs)
conjunction lhs rhs@(Conjunction rcs) = Conjunction (lhs:rcs)
conjunction lhs rhs = Conjunction [lhs, rhs]

disjunction :: Formula -> Formula -> Formula
disjunction lhs@(Disjunction lds) rhs@(Disjunction rds) = Disjunction (lds ++ rds)
disjunction lhs@(Disjunction lds) rhs = Disjunction (rhs:lds)
disjunction lhs rhs@(Disjunction rds) = Disjunction (lhs:rds)
disjunction lhs rhs = Disjunction [lhs, rhs]

negation :: Formula -> Formula
negation = Negation

variable :: String -> Formula
variable = Variable

bottom :: Formula
bottom = Bottom

createAssertion :: (Z3.MonadZ3 z3) => Formula -> Map String Z3.AST -> z3 ()
createAssertion f vs = Z3.assert =<< createZ3Formula f
  where
    createZ3Formula :: (Z3.MonadZ3 z3) => Formula -> z3 Z3.AST 
    createZ3Formula (Implication fs) = List.foldr foldingFunction f' fs'
      where
        z3Formulae = map createZ3Formula fs
        (fs', f') = (init z3Formulae, last z3Formulae)
      
        foldingFunction :: (Z3.MonadZ3 z3) => z3 Z3.AST -> z3 Z3.AST -> z3 Z3.AST
        foldingFunction e c = do { x <- e; y <- c; Z3.mkImplies x y }

    createZ3Formula (Conjunction fs) = List.foldl' foldingFunction f' fs'
      where
        z3Formulae = map createZ3Formula fs
        (f', fs') = (head z3Formulae, tail z3Formulae)

        foldingFunction :: (Z3.MonadZ3 z3) => z3 Z3.AST -> z3 Z3.AST -> z3 Z3.AST
        foldingFunction c e = do { x <- c; y <- e; Z3.mkAnd [x, y] }

    createZ3Formula (Disjunction fs) = List.foldl' foldingFunction f' fs'
      where
        z3Formulae = map createZ3Formula fs
        (f', fs') = (head z3Formulae, tail z3Formulae)

        foldingFunction :: (Z3.MonadZ3 z3) => z3 Z3.AST -> z3 Z3.AST -> z3 Z3.AST
        foldingFunction c e = do { x <- c; y <- e; Z3.mkOr [x, y] }

    createZ3Formula (Negation f) = Z3.mkNot =<< createZ3Formula f
    createZ3Formula (Variable name) = return $ vs ! name
    createZ3Formula Bottom = Z3.mkFalse
  

isFlatClause :: Formula -> Bool
isFlatClause (Implication [Conjunction _, Disjunction _]) = True
isFlatClause _ = False

isImplClause :: Formula -> Bool
isImplClause (Implication [Implication [Variable _, Variable _], Variable _]) = True
isImplClause _ = False

