{-# LANGUAGE FlexibleInstances #-}

module Refactoring.Sequent.Annotated(module Refactoring.Sequent.Annotated) where

import Fmt
import Z3.Base

import Data.Bifunctor (Bifunctor(..))


data Annotated_ a b = Annotated {
  annotation :: a,
  annotated :: b
}

instance Functor (Annotated_ a) where
  fmap f (Annotated a b) = Annotated a (f b)

instance Bifunctor Annotated_ where
  first f (Annotated a b) = Annotated (f a) b
  second = fmap

deriving instance (Eq a, Eq b) => Eq (Annotated_ a b)
deriving instance (Ord a, Ord b) => Ord (Annotated_ a b)

addAnnotation :: c -> Annotated_ a b -> Annotated_ (c, a) b
addAnnotation ann (Annotated a b) = Annotated (ann, a) b

reannotate :: (b -> c) -> Annotated_ a b -> Annotated_ c b
reannotate f (Annotated a b) = (Annotated (f b) b)

deriving instance (Show a, Show b) => Show (Annotated_ a b)

class BuildableAnnotation a where
  buildAnnotation :: a -> Builder

instance {-# OVERLAPPING #-} BuildableAnnotation () where
  buildAnnotation _ = ""

instance {-# OVERLAPPING #-} BuildableAnnotation AST where
  buildAnnotation _ = ""

instance {-# OVERLAPPING #-} (BuildableAnnotation a, BuildableAnnotation b) => BuildableAnnotation (a, b) where
  buildAnnotation (a, b) = buildAnnotation a <> buildAnnotation b

instance {-# OVERLAPPABLE #-} Buildable a => BuildableAnnotation a where
  buildAnnotation a = a |+ ": "

instance (BuildableAnnotation a, Buildable b) => Buildable (Annotated_ a b) where
  build (Annotated a b) = buildAnnotation a +| b |+ ""

