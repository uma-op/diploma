module Main where

import Test.Hspec
import qualified TestClausify
import qualified TestSAT

main :: IO ()
main = hspec $ do
  TestClausify.test_clausify
  TestSAT.test_sat
