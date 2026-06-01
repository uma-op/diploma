{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

module Formula where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)

import qualified Data.List as List
import qualified Z3.Base as Z3
import Control.Monad.State

data PlainFormula = Implication [PlainFormula]
             | Conjunction [PlainFormula]
             | Disjunction [PlainFormula]
             | Atom { atom :: Atom }
             deriving (Eq, Ord)

data Atom = Variable String | Bottom | Top deriving (Eq, Ord)

plainFormulaToString :: PlainFormula -> String
plainFormulaToString (Disjunction ds) = "(" ++ List.intercalate " \\/ " (map plainFormulaToString ds) ++ ")"
plainFormulaToString (Conjunction cs) = "(" ++ List.intercalate " /\\ " (map plainFormulaToString cs) ++ ")"
plainFormulaToString (Implication is) = "(" ++ List.intercalate " => " (map plainFormulaToString is) ++ ")"
plainFormulaToString (Atom (Variable v)) = v 
plainFormulaToString (Atom Top) = "$TOP" 
plainFormulaToString (Atom Bottom) = "$BOT" 

implication :: PlainFormula -> PlainFormula -> PlainFormula
implication lhs rhs@(Implication ris) = Implication (lhs:ris)
implication lhs rhs = Implication [lhs, rhs]

conjunction :: PlainFormula -> PlainFormula -> PlainFormula
conjunction lhs@(Conjunction lcs) rhs@(Conjunction rcs) = Conjunction (lcs ++ rcs)
conjunction lhs@(Conjunction lcs) rhs = Conjunction (rhs:lcs)
conjunction lhs rhs@(Conjunction rcs) = Conjunction (lhs:rcs)
conjunction lhs rhs = Conjunction [lhs, rhs]

disjunction :: PlainFormula -> PlainFormula -> PlainFormula
disjunction lhs@(Disjunction lds) rhs@(Disjunction rds) = Disjunction (lds ++ rds)
disjunction lhs@(Disjunction lds) rhs = Disjunction (rhs:lds)
disjunction lhs rhs@(Disjunction rds) = Disjunction (lhs:rds)
disjunction lhs rhs = Disjunction [lhs, rhs]

negation :: PlainFormula -> PlainFormula
negation = (`implication` bottom)

variable :: String -> PlainFormula
variable = Atom . Variable

bottom :: PlainFormula
bottom = Atom Bottom

top :: PlainFormula
top = Atom Top

asPair :: PlainFormula -> (PlainFormula, PlainFormula)
asPair (Implication [h1, h2]) = (h1, h2)
asPair (Implication (h:t)) = (h, Implication t)
asPair (Conjunction [h1, h2]) = (h1, h2)
asPair (Conjunction (h:t)) = (h, Conjunction t)
asPair (Disjunction [h1, h2]) = (h1, h2)
asPair (Disjunction (h:t)) = (h, Disjunction t)
asPair _ = undefined
  
isAtom :: PlainFormula -> Bool
isAtom (Atom _) = True
isAtom _ = False

atomToAST :: Z3.Context -> Atom -> IO Z3.AST
atomToAST context Top = Z3.mkTrue context
atomToAST context Bottom = Z3.mkFalse context
atomToAST context (Variable vname) = Z3.mkFreshBoolVar context vname

class Formula f where
  plain :: f -> PlainFormula
  atoms :: f -> Set Atom

instance Formula Atom where
  plain = Atom
  atoms = Set.singleton

instance Formula PlainFormula where
  plain = id

  atoms (Implication fs) = foldMap atoms fs
  atoms (Conjunction fs) = foldMap atoms fs
  atoms (Disjunction fs) = foldMap atoms fs
  atoms (Atom a) = Set.singleton a

formulaToString :: Formula a => a -> String
formulaToString = plainFormulaToString . plain
