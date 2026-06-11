module Refactoring.Formula.Formula(module Refactoring.Formula.Formula) where

import Refactoring.Formula.Atom
import Refactoring.Utils.Formatting

import Fmt

data Formula_ =
  Implication [Formula_] |
  Conjunction [Formula_] |
  Disjunction [Formula_] |
  Atom Atom_
  deriving (Eq, Ord, Show)

instance Buildable Formula_ where
  build (Implication is) = "(" +| joinBy " => " is |+ ")"
  build (Conjunction cs) = "(" +| joinBy " /\\ " cs |+ ")"
  build (Disjunction ds) = "(" +| joinBy " \\/ " ds |+ ")"
  build (Atom a) = build a

split :: Formula_ -> (Formula_, Maybe Formula_)
split (Implication [i]) = (i, Nothing)
split (Implication [lhs, rhs]) = (lhs, Just rhs)
split (Implication (lhs : rhs)) = (lhs, Just $ Implication rhs)
split (Conjunction [c]) = (c, Nothing)
split (Conjunction [lhs, rhs]) = (lhs, Just rhs)
split (Conjunction (lhs : rhs)) = (lhs, Just $ Conjunction rhs)
split (Disjunction [d]) = (d, Nothing)
split (Disjunction [lhs, rhs]) = (lhs, Just rhs)
split (Disjunction (lhs : rhs)) = (lhs, Just $ Disjunction rhs)
split a@(Atom _) = (a, Nothing)
split _ = error "Bad formula"

implication :: Formula_ -> Formula_ -> Formula_
implication x (Implication is) = Implication (x : is)
implication x y = Implication [x, y]

top :: Formula_
top = Atom Top

bottom :: Formula_
bottom = Atom Bottom

variable :: String -> Formula_
variable vname = Atom $ Variable vname
