module TestSAT where

import Test.Hspec

import qualified Data.Set as Set

import SAT
import Clausify.FormulaRepr
import Formula

test_sat = describe "SAT" $ do
  test_satProveValid
  test_satProveInvalid

test_satProveValid = it "Proving a -> a" $ do
  let clausified = clausify $ implication (variable "a") (variable "a")
  prove (snd clausified) (fst clausified) Bottom `shouldReturn` Left Set.empty

test_satProveInvalid = it "Proving a -> b" $ do
  let clausified = clausify $ implication (variable "a") (variable "b")
  prove (snd clausified) (fst clausified) Bottom `shouldReturn` Right (Set.fromList [variable "a"])

