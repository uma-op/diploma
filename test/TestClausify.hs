module TestClausify where

import Test.Hspec

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Foldable as Foldable
import qualified Data.Either as Either

import Formula
import Clausify
import Parser (parseFormula)


formulae :: [Formula]
formulae = Either.rights $
           map parseFormula [ "a => b"
                            , "(a => b) => c"
                            , "a \\/ b => c /\\ d"
                            ]

clausified :: [(Set Formula, Set Formula, Formula)]
clausified = [ (Set.empty, Set.singleton $ implication (implication (variable "a") (variable "b")) (variable "$"), variable "$")
             , ( Set.singleton $ implication (conjunction (variable "$p0") (variable "a")) (variable "b")
               , Set.singleton $ implication (implication (variable "$p0") (variable "c")) (variable "$")
               , variable "$"
               )
             , ( Set.fromList [ implication (variable "$p0") (disjunction (variable "a") (variable "b"))
                              , implication (conjunction (variable "c") (variable "d")) (variable "$p1")]
               , Set.singleton $ implication (implication (variable "$p0") (variable "$p1")) (variable "$")
               , variable "$")
             ]

test_clausify = describe "Clausify" $ do
  it "simple" $ do
    Foldable.foldr1 (>>) $ zipWith shouldBe (map clausify formulae) clausified
