{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Refactoring.Clause.Impl(module Refactoring.Clause.Impl) where

import Data.Bifunctor

import Refactoring.Formula.Atom (Atom_)
import Refactoring.Sequent.Annotated

import Fmt

data Impl_ a = Impl (Annotated_ a Atom_) (Annotated_ a Atom_) (Annotated_ a Atom_)
deriving instance Show a => Show (Impl_ a) 

instance Functor Impl_ where
  fmap f (Impl a b c) = Impl (first f a) (first f b) (first f c)

instance Buildable (Impl_ a) where
  build (Impl a b c) = "(" +| annotated a |+ " => " +| annotated b |+ ") => " +| annotated c |+ ""
