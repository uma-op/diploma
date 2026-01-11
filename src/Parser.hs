module Parser where

import Text.Parsec.Char (string, letter, spaces)
import Text.Parsec.String (Parser)
import Control.Monad (void)
import Control.Applicative (many, (<|>))
import qualified Data.Foldable as Foldable
import Formula (Formula (Bottom), variable, negation, conjunction, disjunction, implication)
import Text.Parsec.Error (ParseError)
import Text.Parsec (parse, eof, try)

bot :: Parser Formula
bot = do
  spaceSurroundedSign "_|_"
  return Bottom

var :: Parser Formula
var = do
  name <- many letter
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

unit :: Parser Formula
unit = do lparen
          formula <- implications
          rparen
          return formula
       <|> var
       <|> bot

negations :: Parser Formula
negations = do negationSign
               negation <$> negations
            <|> unit

conjunctions :: Parser Formula
conjunctions = do ns <- negations
                  cs' <- conjunctions'
                  return $ Foldable.foldr1 conjunction (ns:cs')
               where
                 conjunctions' :: Parser [Formula]
                 conjunctions' = many conjunction'

                 conjunction' :: Parser Formula
                 conjunction' = do conjunctionSign
                                   negations

disjunctions :: Parser Formula
disjunctions = do cs <- conjunctions
                  ds' <- disjunctions'
                  return $ Foldable.foldr1 disjunction (cs:ds')
               where
                 disjunctions' :: Parser [Formula]
                 disjunctions' = many disjunction'

                 disjunction' :: Parser Formula
                 disjunction' = do disjunctionSign
                                   conjunctions

implications :: Parser Formula
implications = do ds <- disjunctions
                  is' <- implications'
                  return $ Foldable.foldr1 implication (ds:is')
               where
                 implications' :: Parser [Formula]
                 implications' = many implication'

                 implication' :: Parser Formula
                 implication' = do implicationSign
                                   disjunctions

parseFormula :: String -> Either ParseError Formula
parseFormula = parse (implications <* eof) ""
