module Main(main) where

import Prover
import Formula

formula :: Formula
formula = implication (negation (variable "a")) $ implication (variable "a") (variable "b")

main :: IO ()
main = do
  result <- prove formula
  putStrLn $ "RESULT: " ++ show result
