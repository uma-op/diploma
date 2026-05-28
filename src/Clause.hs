module Clause where

import qualified Z3.Base as Z3

import Data.Set (Set)
import qualified Data.Set as Set

import Formula (Formula(..))
import qualified Formula

data FlatClauseFormula = FlatClauseFormula {
  conjunctFormulas :: [Formula],
  disjunctFromulas :: [Formula]
}

instance Show FlatClauseFormula where
  show c = show $ Implication [Conjunction (conjunctFormulas c), Disjunction (disjunctFromulas c)]

data ImplClauseFormula = ImplClauseFormula {
  aFormula :: Formula, bFormula :: Formula, cFormula :: Formula
}

instance Show ImplClauseFormula where
  show c = show $ Implication [Implication [aFormula c, bFormula c], cFormula c]

flatClauseFromFormula :: Formula -> Maybe FlatClauseFormula
flatClauseFromFormula (Implication [Conjunction cs, Disjunction ds]) =
  if all Formula.isAtom (cs ++ ds)
    then
      Just FlatClauseFormula {
        conjunctFormulas = cs, disjunctFromulas = ds
      }
    else Nothing

flatClauseFromFormula (Implication [Conjunction cs, g]) = 
  if all Formula.isAtom cs && Formula.isAtom g
    then
      Just FlatClauseFormula {
        conjunctFormulas = cs, disjunctFromulas = [g]
      }
    else Nothing

flatClauseFromFormula (Implication [f, Disjunction ds]) =
  if Formula.isAtom f && all Formula.isAtom ds
    then
      Just FlatClauseFormula {
        conjunctFormulas = [f], disjunctFromulas = ds
      }
    else Nothing

flatClauseFromFormula (Implication [f, g]) = 
  if Formula.isAtom f && Formula.isAtom g
    then
      Just FlatClauseFormula {
        conjunctFormulas = [f],
        disjunctFromulas = [g]
      }
    else Nothing

flatClauseFromFormula (Disjunction ds) =
  if all Formula.isAtom ds
    then
      Just FlatClauseFormula {
        conjunctFormulas = [], disjunctFromulas = ds
      }
    else Nothing

flatClauseFromFormula f =
  if Formula.isAtom f
    then Just FlatClauseFormula { conjunctFormulas = [], disjunctFromulas = [f] }
    else Nothing

implClauseFromFormula :: Formula -> Maybe ImplClauseFormula
implClauseFromFormula (Implication [Implication [x, y], z]) =
  if Formula.isAtom x && Formula.isAtom y && Formula.isAtom z
    then Just ImplClauseFormula { aFormula = x, bFormula = y, cFormula = z }
    else Nothing

implClauseFromFormula _ = Nothing

implImpliesFlat :: ImplClauseFormula -> FlatClauseFormula
implImpliesFlat impl = FlatClauseFormula { conjunctFormulas = [bFormula impl], disjunctFromulas = [cFormula impl]}

class Clause c where
  variables :: c -> Set Formula

instance Clause FlatClauseFormula where
  variables flat@(FlatClauseFormula cs ds) = Set.unions $ map Formula.variables (cs ++ ds)

instance Clause ImplClauseFormula where
  variables impl@(ImplClauseFormula a b c) = Set.fromList [a, b, c]
