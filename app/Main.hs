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
  let formula = Implication [Conjunction [a, a], a]

  prove formula

foo = \_43 -> (_43 $ const (Right (\_6 -> (_43(\_8 -> Left (\_7 -> (_8(_7, _6))))))))
bar = \_22 -> (_22 $ const (Right (\_8 -> (_22(\_9 -> Left (\_7 -> (_9(_7, _8))))))))
