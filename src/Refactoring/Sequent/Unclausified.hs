{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Refactoring.Sequent.Unclausified(module Refactoring.Sequent.Unclausified) where

import Data.Bifunctor

import Refactoring.Formula.Atom (Atom_)
import Refactoring.Clause.Flat (Flat_)
import Refactoring.Clause.Impl (Impl_)
import Refactoring.Formula.Formula (Formula_)
import Refactoring.Utils.Formatting (joinByComma)
import Refactoring.Sequent.Annotated

import Fmt

data Unclausified_ a c =
  Unclausified
    [Annotated_ a (Flat_ c)]
    [Annotated_ a (Impl_ c)]
    [Annotated_ a Formula_]
    (Annotated_ (a, c) Atom_)

instance Functor (Unclausified_ a) where
  fmap f (Unclausified flats impls uncs goal) = 
    Unclausified
      (second (fmap f) <$> flats)
      (second (fmap f) <$> impls)
      uncs
      (first (second f) goal)

instance Bifunctor Unclausified_ where
  first f (Unclausified flats impls uncs goal) =
    Unclausified  
      (first f <$> flats)
      (first f <$> impls)
      (first f <$> uncs)
      (first (first f) goal)
  second = fmap

deriving instance (Show a, Show c) => Show (Unclausified_ a c)

instance (BuildableAnnotation a, BuildableAnnotation c) => Buildable (Unclausified_ a c) where
  build (Unclausified flats impls unclausified goal) = 
    "R{" +| joinByComma flats |+
    "} X{" +| joinByComma impls |+
    "} U{" +| joinByComma unclausified |+
    "} |- " +| goal |+ ""
    
