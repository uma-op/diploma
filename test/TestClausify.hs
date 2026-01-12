module TestClausify where

import Test.Hspec

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Foldable as Foldable

import Formula
import Clausify


formulae :: [Formula]
formulae = [ implication (variable "a") (variable "b")
           , implication (implication (variable "a") (variable "b")) (variable "c")
           ]

clausified :: [(Set Formula, Set Formula, Formula)]
clausified = [ (Set.empty, Set.singleton $ implication (implication (variable "a") (variable "b")) (variable "$"), variable "$")
             , ( Set.singleton $ implication (conjunction (variable "$p0") (variable "a")) (variable "b")
               , Set.singleton $ implication (implication (variable "$p0") (variable "c")) (variable "$")
               , variable "$"
               )
             ]

test_clausify = describe "Clausify" $ do
  test_clausifyIdempotence


test_clausifyIdempotence = it "Clausify idempotence" $ do
  Foldable.foldr1 (>>) $ zipWith shouldBe (map clausify formulae) clausified
