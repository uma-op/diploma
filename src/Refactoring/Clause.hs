{-# LANGUAGE FlexibleInstances #-}

module Refactoring.Clause(module Refactoring.Clause) where

import Refactoring.Sequent.Annotated
import Refactoring.Formula
import Refactoring.Formula.Formula
import Refactoring.Formula.Atom
import Refactoring.Clause.Flat
import Refactoring.Clause.Impl
import Control.Monad.Identity (Identity(..))

class Clause c where
  fromFormula :: Formula_ -> Maybe c
  toFormula :: c -> Formula_

isAtom :: Formula_ -> Bool
isAtom (Atom _) = True
isAtom _ = False

disjunctionAtoms :: Formula_ -> Maybe [Atom_] 
disjunctionAtoms (Atom a) = Just [a]
disjunctionAtoms (Disjunction ds) = if all isAtom ds then Just (ds >>= atoms) else Nothing
disjunctionAtoms _ = Nothing

conjunctionAtoms :: Formula_ -> Maybe [Atom_]
conjunctionAtoms (Atom a) = Just [a]
conjunctionAtoms (Conjunction cs) = if all isAtom cs then Just (cs >>= atoms) else Nothing
conjunctionAtoms _ = Nothing

instance Clause (Flat_ ()) where
  fromFormula (Implication [c, d]) = do
    cAtoms <- conjunctionAtoms c
    dAtoms <- disjunctionAtoms d
    return $ Flat (Annotated () <$> cAtoms) (Annotated () <$> dAtoms)
  fromFormula d = do
    dAtoms <- disjunctionAtoms d
    return $ Flat [] (Annotated () <$> dAtoms)

  toFormula (Flat cs ds) = 
    Implication [
      Conjunction $ Atom . annotated <$> cs,
      Disjunction $ Atom . annotated <$> ds
    ]

instance Clause (Impl_ ()) where
  fromFormula (Implication [Implication [Atom a, Atom b], Atom c]) = Just $
    Impl (Annotated () a) (Annotated () b) (Annotated () c) 
  fromFormula _ = Nothing

  toFormula (Impl (Annotated () a) (Annotated () b) (Annotated () c)) = Implication [Implication [Atom a, Atom b], Atom c]

