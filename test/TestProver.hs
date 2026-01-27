module TestProver where

import Test.Hspec

import qualified Data.Set as Set
import qualified Data.Foldable as Foldable

import Prover
import Formula
import Parser (parseFormulaWithError)

test_sat = describe "SAT" $ do
  --it "Prove" $ do
  --  prove (implication (negation (variable "A")) (implication (variable "A") (variable "B"))) `shouldReturn` Yes Set.empty
  test_satProveValid
  test_satProveInvalid

test_satProveValid = Foldable.foldr1 (>>) (map test_satProveValidFormula validIntuitionistic)
  where
    test_satProveValidFormula formula = it ("Proving " ++ show formula) $ do
      prove formula `shouldReturn` Yes Set.empty

test_satProveInvalid = Foldable.foldr1 (>>) (map test_satProveInvalidFormula invalidIntuitionistic)
  where
    test_satProveInvalidFormula formula = it ("Invalidating " ++ show formula) $ do
      prove formula `shouldReturn` No Set.empty

validIntuitionistic :: [Formula]
validIntuitionistic = map parseFormulaWithError
  [ "A => A"
  , "A /\\ B => A"
  , "A /\\ B => B"
  , "A => A \\/ B"
  , "B => A \\/ B"
  , "(A => B) /\\ (B => C) => (A => C)"
  , "A /\\ (B \\/ C) => (A /\\ B) \\/ (A /\\ C)"
  , "(A => B) => (-B => -A)"
  , "A /\\ (A => B) => B"
  , "_|_ => A"
  , "-A => (A => B)"
  , "A => --A"
  , "(A => _|_) => -A"
  , "A /\\ -A => _|_"
  , "(A => B) => ((A => -B) => -A)"
  , "((A \\/ B) => C) => ((A => C) \\/ (B => C))"  
  ]
  
invalidIntuitionistic :: [Formula]
invalidIntuitionistic = map parseFormulaWithError
  [ "A \\/ -A"
  , "--A => A"
  , "((A => _|_) => _|_) => A"
  , "((A => B) => A) => A"
  , "-(A /\\ B) => (-A \\/ -B)"
  , "-(-A \\/ -B) => A /\\ B"
  , "(A => B) \\/ (B => A)"
  , "(A => B) => (-A \\/ B)"
  , "-(A => B) => A"
  ]

mixedIntuitionistic :: [Formula]
mixedIntuitionistic = map parseFormulaWithError
  [ "-(A \\/ B) => -A /\\ -B"
  , "(-A /\\ -B) => -(A \\/ B)"
  , "-(A => B) => (A /\\ -B)"
  , "(A => (B \\/ C)) => ((A => B) \\/ (A => C))"
  , "(A /\\ B => C) => (A => B => C)"
  ]
