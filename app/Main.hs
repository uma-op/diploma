module Main(main) where

import Prover
import Formula

formula :: Formula
formula = implication (variable "a") (implication (implication (variable "a") (variable "b")) (variable "b"))

main :: IO ()
main = do
  result <- prove formula
  putStrLn $ "RESULT: " ++ show result
