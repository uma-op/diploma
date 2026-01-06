module TestClausify where

import Test.Hspec

import qualified Data.Set as Set
import Data.Set (Set)

import Formula
import Clausify.FormulaRepr


formulae :: [Formula]
formulae = [ implication (variable "a") (variable "b")
           , implication (implication (variable "a") (variable "b")) (variable "c")
           ]

clausified :: [(Set Formula, Set Formula)]
clausified = [ (Set.singleton $ implication (variable "a") (variable "b"), Set.empty)
             , (Set.empty, Set.singleton $ implication (implication (variable "a") (variable "b")) (variable "c"))
             ]

test_clausify = describe "Clausify" $ do
  test_clausifyIdempotence


test_clausifyIdempotence = it "Clausify idempotence" $ do
  map clausify formulae `shouldBe` clausified
