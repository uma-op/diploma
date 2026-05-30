module Parser(parseFormula, parseFormulaWithError) where

import Text.Parsec.Char (string, letter, spaces)
import Text.Parsec.String (Parser)
import Control.Applicative (many, (<|>))
import qualified Data.Foldable as Foldable
import Formula (PlainFormula, bottom, variable, conjunction, disjunction, implication)
import Text.Parsec.Error (ParseError)
import Text.Parsec (parse, eof, try, many1)

var :: Parser PlainFormula
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

unit :: Parser PlainFormula
unit = do lparen
          formula <- implications
          rparen
          return formula
       <|> var

negations :: Parser PlainFormula
negations = do negationSign
               flip implication bottom <$> negations
            <|> unit

conjunctions :: Parser PlainFormula
conjunctions = do ns <- negations
                  cs' <- conjunctions'
                  return $ Foldable.foldr1 conjunction (ns:cs')
               where
                 conjunctions' :: Parser [PlainFormula]
                 conjunctions' = many conjunction'

                 conjunction' :: Parser PlainFormula
                 conjunction' = do conjunctionSign
                                   negations

disjunctions :: Parser PlainFormula
disjunctions = do cs <- conjunctions
                  ds' <- disjunctions'
                  return $ Foldable.foldr1 disjunction (cs:ds')
               where
                 disjunctions' :: Parser [PlainFormula]
                 disjunctions' = many disjunction'

                 disjunction' :: Parser PlainFormula
                 disjunction' = do disjunctionSign
                                   conjunctions

implications :: Parser PlainFormula
implications = do ds <- disjunctions
                  is' <- implications'
                  return $ Foldable.foldr1 implication (ds:is')
               where
                 implications' :: Parser [PlainFormula]
                 implications' = many implication'

                 implication' :: Parser PlainFormula
                 implication' = do implicationSign
                                   disjunctions

parseFormula :: String -> Either ParseError PlainFormula
parseFormula = parse (implications <* eof) ""

parseFormulaWithError :: String -> PlainFormula
parseFormulaWithError = handler . parseFormula
  where
    handler :: Either ParseError PlainFormula -> PlainFormula
    handler (Left e) = error $ show e
    handler (Right f) = f
