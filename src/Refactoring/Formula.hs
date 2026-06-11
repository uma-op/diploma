{-# LANGUAGE OverloadedStrings #-}

module Refactoring.Formula(module Refactoring.Formula) where

import qualified Data.Set as Set

import Refactoring.Formula.Atom
import Refactoring.Formula.Formula

class Formula f where
  atoms :: f -> [Atom_]

instance Formula Formula_ where
  atoms = Set.toList . Set.fromList . atoms'
    where
      atoms' :: Formula_ -> [Atom_]
      atoms' (Atom a) = [a]
      atoms' (Implication is) = is >>= atoms'
      atoms' (Disjunction ds) = ds >>= atoms'
      atoms' (Conjunction cs) = cs >>= atoms'

instance Formula Atom_ where
  atoms = (:[])

