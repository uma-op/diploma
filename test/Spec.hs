module Main where

import Test.Hspec
import qualified TestClausify
import qualified TestProver
import qualified TestParser

main :: IO ()
main = hspec $ do
  TestClausify.test_clausify
  TestProver.test_sat
  TestParser.tests_parser
