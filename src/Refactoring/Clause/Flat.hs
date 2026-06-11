{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Refactoring.Clause.Flat(module Refactoring.Clause.Flat) where

import Data.Bifunctor

import Refactoring.Formula.Atom
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
