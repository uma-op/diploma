module Refactoring.Parser(parseFormula, parseFormulaWithError) where

import Text.Parsec.Char (string, letter, spaces)
import Text.Parsec.String (Parser)
import Control.Applicative (many, (<|>))
import qualified Data.Foldable as Foldable
import Refactoring.Formula.Formula
import Text.Parsec.Error (ParseError)
import Text.Parsec (parse, eof, try, many1)

var :: Parser Formula_
var = do
  name <- many1 letter
  return $ variable name

spaceSurroundedSign :: String -> Parser ()
spaceSurroundedSign sign = spaces >> string sign >> spaces

implicationSign :: Parser ()
implicationSign = try $ spaceSurroundedSign "=>"

disjunctionSign :: Parser ()
disjunctionSign = try $ spaceSurroundedSign "\\/"

conjunctionSign :: Parser ()
conjunctionSign = try $ spaceSurroundedSign "/\\"

negationSign :: Parser ()
negationSign = try $ spaceSurroundedSign "-"

lparen :: Parser ()
lparen = try $ spaceSurroundedSign "("

rparen :: Parser ()
rparen = try $ spaceSurroundedSign ")"

unit :: Parser Formula_
unit = do lparen
          formula <- implications
          rparen
          return formula
       <|> var

negations :: Parser Formula_
negations = do negationSign
               flip implication bottom <$> negations
            <|> unit

conjunctions :: Parser Formula_
conjunctions = do ns <- negations
                  cs' <- conjunctions'
                  return $ Foldable.foldr1 conjunction (ns:cs')
               where
                 conjunctions' :: Parser [Formula_]
                 conjunctions' = many conjunction'

                 conjunction' :: Parser Formula_
                 conjunction' = do conjunctionSign
                                   negations

disjunctions :: Parser Formula_
disjunctions = do cs <- conjunctions
                  ds' <- disjunctions'
                  return $ Foldable.foldr1 disjunction (cs:ds')
               where
                 disjunctions' :: Parser [Formula_]
                 disjunctions' = many disjunction'

                 disjunction' :: Parser Formula_
                 disjunction' = do disjunctionSign
                                   conjunctions

implications :: Parser Formula_
implications = do ds <- disjunctions
                  is' <- implications'
                  return $ Foldable.foldr1 implication (ds:is')
               where
                 implications' :: Parser [Formula_]
                 implications' = many implication'

                 implication' :: Parser Formula_
                 implication' = do implicationSign
                                   disjunctions

parseFormula :: String -> Either ParseError Formula_
parseFormula = parse (implications <* eof) ""

parseFormulaWithError :: String -> Formula_
parseFormulaWithError = handler . parseFormula
  where
    handler :: Either ParseError Formula_ -> Formula_
    handler (Left e) = error $ show e
    handler (Right f) = f
