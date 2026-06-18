module Main(main) where

import Refactoring.Formula.Formula
import Refactoring.Prover.Prover (prove)
import Refactoring.Parser (parseFormulaWithError)

main :: IO ()
main = do
  let formula = Disjunction [
        Implication [variable "a", bottom], variable "a"]

  let a = variable "a"
  let b = variable "b"
  let formula = Implication [Implication [Implication [a, b], a], a]
  let formula = Implication [Implication [Implication [Implication [Implication [a, b], a], a], b], b]
  let formula = Implication [a, a]
  let formula = Implication [Implication [Disjunction [a, Implication [a, b]], b], b]
  let c = variable "c"
  let d = variable "d"
  let formula =
        Implication [
          Implication [
            Implication [
              Implication [Conjunction [a, b], d],
              Disjunction [
                Implication [a, d],
                Implication [b, c]
              ]], c], c]
  -- let formula = Implication [Conjunction [a, a], a]
  -- let formula = Disjunction [a, Implication [a, bottom]] 
  let formula = parseFormulaWithError "(a /\\ a) => a"

  prove formula
