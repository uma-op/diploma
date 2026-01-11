module Main(main) where

import Prover
import Formula

formula :: Formula
formula = implication (variable "a") $ implication (variable "b") (variable "a")

main :: IO ()
main = do
  result <- prove formula
  putStrLn $ "RESULT: " ++ show result
