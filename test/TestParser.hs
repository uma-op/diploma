module TestParser (tests_parser) where

import Test.Hspec
import qualified Data.Either as Either

import Formula
import Parser

tests_parser = describe "Parser" $ do
  it "parsing correct" $ do
    Either.rights (map parseFormula input) `shouldBe` output

input :: [String]
input = [ "A"
        , "_|_"
        , "-A"
        , "-_|_"
        , "A \\/ B"
        , "A /\\ B"
        , "A => B"
        , "-A \\/ B"
        , "-(A \\/ B)"
        , "-A /\\ B"
        , "-(A /\\ B)"
        , "A /\\ -B"
        , "A => -B"
        , "-A => B"
        , "-(A => B)"
        , "-(_|_)"
        , "A \\/ _|_"
        , "A /\\ _|_"
        , "_|_ => A"
        , "A => _|_"
        , "A /\\ B \\/ C"
        , "A \\/ B /\\ C"
        , "A => B => C"
        , "A /\\ B => C"
        , "A => B /\\ C"
        , "(A)"
        , "(_|_)"
        , "(-A)"
        , "(A \\/ B)"
        , "(A /\\ B) \\/ C"
        , "A /\\ (B \\/ C)"
        , "(A \\/ B) /\\ (C \\/ D)"
        , "((A))"
        , "((A \\/ B) /\\ C) => D"
        , "A /\\ (B /\\ (C /\\ D))"
        , "(A \\/ (B \\/ C)) => D"
        , "((A => B) /\\ C) \\/ D"
        , "A => (B => (C => D))"
        , "(A /\\ B) => (C \\/ D)"
        , "(A \\/ B) => (C /\\ D)"
        , "((A /\\ B) => C) /\\ (D => E)"
        , "(A => B) => (C => D)"
        , "((A \\/ B) /\\ (C \\/ D)) => (E /\\ F)"
        , "(((A)))"
        , "(A /\\ (B \\/ (C => D)))"
        , "A => (B /\\ (C \\/ D))"
        , "(A => B) \\/ (C => D)"
        , "((A /\\ B) \\/ C) => (D /\\ (E \\/ F))"
        , "-((A /\\ B) \\/ C)"
        , "-(A /\\ -B)"
        , "-(-A)"
        , "--A"
        , "-(A => _|_)"
        , "(-A => _|_) => A"
        , "A => (-B => _|_)"
        ]

output :: [Formula]
output = [ variable "A"
         , bottom
         , negation (variable "A")
         , negation bottom
         , disjunction (variable "A") (variable "B")
         , conjunction (variable "A") (variable "B")
         , implication (variable "A") (variable "B")
         , disjunction (negation (variable "A")) (variable "B")
         , negation (disjunction (variable "A") (variable "B"))
         , conjunction (negation (variable "A")) (variable "B")
         , negation (conjunction (variable "A") (variable "B"))
         , conjunction (variable "A") (negation (variable "B"))
         , implication (variable "A") (negation (variable "B"))
         , implication (negation (variable "A")) (variable "B")
         , negation (implication (variable "A") (variable "B"))
         , negation bottom
         , disjunction (variable "A") bottom
         , conjunction (variable "A") bottom
         , implication bottom (variable "A")
         , implication (variable "A") bottom
         , disjunction (conjunction (variable "A") (variable "B")) (variable "C")
         , disjunction (variable "A") (conjunction (variable "B") (variable "C"))
         , implication (variable "A") (implication (variable "B") (variable "C"))
         , implication (conjunction (variable "A") (variable "B")) (variable "C")
         , implication (variable "A") (conjunction (variable "B") (variable "C"))
         , variable "A"
         , bottom
         , negation (variable "A")
         , disjunction (variable "A") (variable "B")
         , disjunction (conjunction (variable "A") (variable "B")) (variable "C")
         , conjunction (variable "A") (disjunction (variable "B") (variable "C"))
         , conjunction (disjunction (variable "A") (variable "B")) (disjunction (variable "C") (variable "D"))
         , variable "A"
         , implication (conjunction (disjunction (variable "A") (variable "B")) (variable "C")) (variable "D")
         , conjunction (variable "A") (conjunction (variable "B") (conjunction (variable "C") (variable "D")))
         , implication (disjunction (variable "A") (disjunction (variable "B") (variable "C"))) (variable "D")
         , disjunction (conjunction (implication (variable "A") (variable "B")) (variable "C")) (variable "D")
         , implication (variable "A") (implication (variable "B") (implication (variable "C") (variable "D")))
         , implication (conjunction (variable "A") (variable "B")) (disjunction (variable "C") (variable "D"))
         , implication (disjunction (variable "A") (variable "B")) (conjunction (variable "C") (variable "D"))
         , conjunction (implication (conjunction (variable "A") (variable "B")) (variable "C")) (implication (variable "D") (variable "E"))
         , implication (implication (variable "A") (variable "B")) (implication (variable "C") (variable "D"))
         , implication (conjunction (disjunction (variable "A") (variable "B")) (disjunction (variable "C") (variable "D"))) (conjunction (variable "E") (variable "F"))
         , variable "A"
         , conjunction (variable "A") (disjunction (variable "B") (implication (variable "C") (variable "D")))
         , implication (variable "A") (conjunction (variable "B") (disjunction (variable "C") (variable "D")))
         , disjunction (implication (variable "A") (variable "B")) (implication (variable "C") (variable "D"))
         , implication (disjunction (conjunction (variable "A") (variable "B")) (variable "C")) (conjunction (variable "D") (disjunction (variable "E") (variable "F")))
         , negation (disjunction (conjunction (variable "A") (variable "B")) (variable "C"))
         , negation (conjunction (variable "A") (negation (variable "B")))
         , negation (negation (variable "A"))
         , negation (negation (variable "A"))
         , negation (implication (variable "A") bottom)
         , implication (implication (negation (variable "A")) bottom) (variable "A")
         , implication (variable "A") (implication (negation (variable "B")) bottom)
         ]
