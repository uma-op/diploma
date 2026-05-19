module Main(main) where

import Clausify (clausify)
import Formula (implication, disjunction, variable, negation, bottom)
import Parser (parseFormula)
import qualified Data.Either as Either

main :: IO ()
main = do
  -- ((a v (a -> b)) -> b) -> b
  print $ clausify $ Either.fromRight undefined $ parseFormula "a \\/ -a"

{-
  config <- mkConfig
  setParamValue config "proof" "true"

  context <- mkContext config
  a <- mkFreshBoolVar context "a"
  not_a <- mkNot context a
  solver <- mkSolver context
  assertion <- mkAnd context [a, not_a]
  solverAssertCnstr context solver assertion

  result <- solverCheck context solver
  putStrLn $ "Result: " ++ show result
  proof <- solverGetProof context solver
  proofString <- astToString context proof
  putStrLn $ "Proof: " ++ proofString

-}
  return ()
