module TestParser (tests_parser) where

import Test.Hspec

import Formula
import Parser

tests_parser = describe "Parser" $ do
  test_parseSimple

test_parseSimple = it "Parse simple" $ do
  parseFormula "a => b" `shouldBe` Right (implication (variable "a") (variable "b"))
