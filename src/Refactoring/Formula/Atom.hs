module Refactoring.Formula.Atom(module Refactoring.Formula.Atom) where

import Data.String
import Fmt

data Atom_ = Top | Bottom | Variable String deriving (Eq, Ord, Show)

instance Buildable Atom_ where
  build (Variable vname) = fromString vname
  build Top = "$TOP"
  build Bottom = "$BOT"
