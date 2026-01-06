module Main(main) where

import SAT
import Clausify.FormulaRepr
import Clausify.ParseProblem
import Formula (Formula(Bottom), implication, variable)

import qualified Data.Bifunctor as Bifunctor
import Data.Set(Set)
import qualified Data.Set as Set

formula :: Formula
formula = (implication (variable "a") (variable "b"))

flats, impls :: Set Formula
(flats, impls) = clausify formula

main :: IO ()
main = do
  print flats
  print impls
  result <- prove impls flats Bottom
  print result
