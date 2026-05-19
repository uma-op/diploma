module Formula where

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map, (!))
import qualified Data.List as List

import qualified Z3.Monad as Z3
import Z3.Monad (AST)
import Data.Function (on)

newtype Variables = Variables (Map String AST)

data Formula = Implication [Formula]
             | Conjunction [Formula]
             | Disjunction [Formula]
             | Negation Formula
             | Variable String
             deriving (Eq)

instance Show Formula where
  show (Variable name) = name
  show (Negation f) = "-" ++ show f
  show (Disjunction ds) = "(" ++ List.intercalate " \\/ " (map show ds) ++ ")"
  show (Conjunction cs) = "(" ++ List.intercalate " /\\ " (map show cs) ++ ")"
  show (Implication is) = "(" ++ List.intercalate " => " (map show is) ++ ")"

instance Ord Formula where
  compare = on compare show

variables :: Formula -> Set String
variables (Implication fs) = foldMap variables fs
variables (Conjunction fs) = foldMap variables fs
variables (Disjunction fs) = foldMap variables fs
variables (Negation fs) = variables fs
variables (Variable vname) = Set.singleton vname

implication :: Formula -> Formula -> Formula
implication lhs rhs@(Implication ris) = Implication (lhs:ris)
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
bottom = variable "$BOT"

top :: Formula
top = variable "$TOP"

asPair :: Formula -> (Formula, Formula)
asPair (Implication [h1, h2]) = (h1, h2)
asPair (Implication (h:t)) = (h, Implication t)
asPair (Conjunction [h1, h2]) = (h1, h2)
asPair (Conjunction (h:t)) = (h, Conjunction t)
asPair (Disjunction [h1, h2]) = (h1, h2)
asPair (Disjunction (h:t)) = (h, Disjunction t)
asPair _ = undefined

createAssertion :: (Z3.MonadZ3 z3) => Formula -> Variables -> z3 ()
createAssertion f (Variables vs) = Z3.assert =<< createZ3Formula f
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
    createZ3Formula (Variable "$BOT") = Z3.mkFalse
    createZ3Formula (Variable "$TOP") = Z3.mkTrue
    createZ3Formula (Variable name) = return $ vs ! name
  
isAtom :: Formula -> Bool
isAtom (Variable _) = True
isAtom _ = False

isFlatClause :: Formula -> Bool
isFlatClause (Implication [Conjunction cs, Disjunction ds]) = all isAtom (cs ++ ds)
isFlatClause (Implication [Conjunction cs, g]) = all isAtom cs && isAtom g
isFlatClause (Implication [f, Disjunction ds]) = isAtom f && all isAtom ds
isFlatClause (Implication [f, g]) = isAtom f && isAtom g
isFlatClause (Disjunction ds) = all isAtom ds
isFlatClause f = isAtom f

isImplClause :: Formula -> Bool
isImplClause (Implication [Implication [x, y], z]) = isAtom x && isAtom y && isAtom z
isImplClause _ = False

