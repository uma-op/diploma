{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Refactoring.Clause.Flat(module Refactoring.Clause.Flat) where

import Data.Bifunctor

import Refactoring.Formula.Atom
import Refactoring.Formula.Formula
import Refactoring.Formula

import Refactoring.Utils.Formatting
import Refactoring.Sequent.Annotated
import Refactoring.Clause.Impl

import Fmt

data Flat_ a = Flat [Annotated_ a Atom_] [Annotated_ a Atom_] deriving (Eq, Ord)

instance Functor Flat_ where
  fmap f (Flat cs ds) = Flat (first f <$> cs) (first f <$> ds)

deriving instance Show a => Show (Flat_ a)

instance Buildable (Flat_ a) where
  build (Flat cs ds) = "[" +| joinByComma (annotated <$> cs) |+ "] => [" +| joinByComma (annotated <$> ds) |+ "]" 
  
implImpliesFlat :: Impl_ a -> Flat_ a
implImpliesFlat (Impl a b c) = Flat [b] [c]

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

instance Formula (Flat_ ()) where
  atoms (Flat cs ds) = (annotated <$> cs) ++ (annotated <$> ds)

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

