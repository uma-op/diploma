module TestProver where

import Test.Hspec

import qualified Data.Set as Set
import qualified Data.Foldable as Foldable

import Prover
import Formula
import Parser (parseFormulaWithError)

test_sat = describe "SAT" $ do
  test_satProveStrange
--  test_satProveValid
--  test_satProveInvalid


strange = parseFormulaWithError "((A \\/ B) => C) => ((A => C) \\/ (B => C))"
test_satProveStrange = it ("Proving " ++ show strange) $ do
  prove strange `shouldReturn` No Set.empty

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
  , "-(A \\/ B) => -A /\\ -B"
  , "(-A /\\ -B) => -(A \\/ B)"
  , "(A /\\ B => C) => (A => B => C)"  
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
  , "-(A => B) => (A /\\ -B)"
  , "(A => (B \\/ C)) => ((A => B) \\/ (A => C))"
  ]
