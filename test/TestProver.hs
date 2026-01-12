module TestProver where

import Test.Hspec

import qualified Data.Set as Set

import Prover
import Formula

test_sat = describe "SAT" $ do
  test_satProveValid
  test_satProveInvalid

test_satProveValid = it "Proving a -> a" $ do
  prove (implication (variable "a") (variable "a")) `shouldReturn` Yes Set.empty

test_satProveInvalid = it "Proving a -> b" $ do
  prove (implication (variable "a") (variable "b")) `shouldReturn` No Set.empty

