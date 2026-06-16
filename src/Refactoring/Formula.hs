{-# LANGUAGE OverloadedStrings #-}

module Refactoring.Formula(module Refactoring.Formula) where

import qualified Data.Set as Set

import Refactoring.Formula.Atom
import Refactoring.Formula.Formula

class Formula f where
  atoms :: f -> [Atom_]
  fromFormula :: Formula_ -> Maybe f
  toFormula :: f -> Formula_

instance Formula Formula_ where
  atoms = Set.toList . Set.fromList . atoms'
    where
      atoms' :: Formula_ -> [Atom_]
      atoms' (Atom a) = [a]
      atoms' (Implication is) = is >>= atoms'
      atoms' (Disjunction ds) = ds >>= atoms'
      atoms' (Conjunction cs) = cs >>= atoms'

  fromFormula = Just
  toFormula = id

instance Formula Atom_ where
  atoms = (:[])

  fromFormula (Atom a) = Just a
  fromFormula _ = Nothing

  toFormula = Atom
