module Refactoring.Sequent.Intuit(module Refactoring.Sequent.Intuit) where

import Data.Bifunctor

import Refactoring.Formula.Atom
import Refactoring.Clause.Flat
import Refactoring.Clause.Impl
import Refactoring.Utils.Formatting

import Refactoring.Sequent.Annotated

import Fmt

data Intuit_ a c = Intuit [Annotated_ a (Flat_ c)] [Annotated_ a (Impl_ c)] (Annotated_ (a, c) Atom_)

instance Functor (Intuit_ a) where
  fmap f (Intuit flats impls goal) = Intuit (second (fmap f) <$> flats) (second (fmap f) <$> impls) (first (second f) goal)

instance Bifunctor Intuit_ where
  first f (Intuit flats impls goal) = Intuit (first f <$> flats) (first f <$> impls) (first (first f) goal)
  second = fmap

deriving instance (Show a, Show c) => Show (Intuit_ a c)

instance (BuildableAnnotation a, BuildableAnnotation c) => Buildable (Intuit_ a c) where
  build (Intuit flats impls goal) =
    "R{" +| joinByComma flats |+
    "} X{" +| joinByComma impls |+
    "} |- " +| goal |+ ""
