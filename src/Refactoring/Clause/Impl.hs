{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Refactoring.Clause.Impl(module Refactoring.Clause.Impl) where

import Data.Bifunctor

import Refactoring.Formula.Atom (Atom_)
import Refactoring.Sequent.Annotated
import Refactoring.Formula
import Refactoring.Formula.Formula

import Fmt

data Impl_ a = Impl (Annotated_ a Atom_) (Annotated_ a Atom_) (Annotated_ a Atom_) deriving Eq
deriving instance Show a => Show (Impl_ a) 

instance Functor Impl_ where
  fmap f (Impl a b c) = Impl (first f a) (first f b) (first f c)

instance Buildable (Impl_ a) where
  build (Impl a b c) = "(" +| annotated a |+ " => " +| annotated b |+ ") => " +| annotated c |+ ""

instance Formula (Impl_ ()) where
  atoms (Impl a b c) = [annotated a, annotated b, annotated c]

  fromFormula (Implication [Implication [Atom a, Atom b], Atom c]) = Just $
    Impl (Annotated () a) (Annotated () b) (Annotated () c) 
  fromFormula _ = Nothing

  toFormula (Impl (Annotated () a) (Annotated () b) (Annotated () c)) = Implication [Implication [Atom a, Atom b], Atom c]

