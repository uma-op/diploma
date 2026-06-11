module Main(main) where

import Refactoring.Formula.Formula
import Refactoring.Prover.Prover (prove)


main :: IO ()
main = do
  let formula = Disjunction [
        Implication [variable "a", bottom], variable "a"]

  let a = variable "a"
  let b = variable "b"
  let formula = Implication [Implication [Implication [a, b], a], a]

  let formula = Implication [Implication [Implication [Implication [Implication [a, b], a], a], b], b]
  prove formula

