module Refactoring.Sequent.Classic(module Refactoring.Sequent.Classic) where

import Data.Bifunctor

import Refactoring.Clause.Flat
import Refactoring.Formula.Atom
import Refactoring.Utils.Formatting
import Refactoring.Sequent.Annotated

import Fmt

data Classic_ a c = Classic [Annotated_ a (Flat_ c)] [Annotated_ (a, c) Atom_] (Annotated_ (a, c) Atom_)

instance Functor (Classic_ a) where
  fmap f (Classic flats assumptions goal) =
    Classic
      (second (fmap f) <$> flats)
      (first (second f) <$> assumptions) 
      (first (second f) goal)

instance Bifunctor Classic_ where
  first f (Classic flats assumptions goal) =
    Classic
      (first f <$> flats)
      (first (first f) <$> assumptions)
      (first (first f) goal)
  second = fmap

deriving instance (Show a, Show c) => Show (Classic_ a c)

instance (BuildableAnnotation a, BuildableAnnotation c) => Buildable (Classic_ a c) where
  build (Classic flats assumptions goal) =
    "R{" +| joinByComma flats |+
    "} A{" +| joinByComma assumptions |+
    "} |- " +| goal |+ ""
