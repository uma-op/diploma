module Formula where

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.List as List
import qualified Z3.Base as Z3

import Data.Function (on)

data Formula = Implication [Formula]
             | Conjunction [Formula]
             | Disjunction [Formula]
             | Variable { variableName :: String }
             deriving (Eq)

instance Show Formula where
  show (Variable name) = name
  show (Disjunction ds) = "(" ++ List.intercalate " \\/ " (map show ds) ++ ")"
  show (Conjunction cs) = "(" ++ List.intercalate " /\\ " (map show cs) ++ ")"
  show (Implication is) = "(" ++ List.intercalate " => " (map show is) ++ ")"

instance Ord Formula where
  compare = on compare show

variables :: Formula -> Set Formula
variables (Implication fs) = foldMap variables fs
variables (Conjunction fs) = foldMap variables fs
variables (Disjunction fs) = foldMap variables fs
variables v = Set.singleton v

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
negation = (`implication` bottom)

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
  
isAtom :: Formula -> Bool
isAtom (Variable _) = True
isAtom _ = False

atomToAST :: Z3.Context -> Formula -> IO Z3.AST
atomToAST context (Variable "$TOP") = Z3.mkTrue context
atomToAST context (Variable "$BOT") = Z3.mkFalse context
atomToAST context (Variable vname) = Z3.mkFreshBoolVar context vname
atomToAST _ _ = error "Formula is not atom"

