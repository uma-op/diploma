module Main where

import ParseProblem (Form(..))
import qualified Clausify as C
import FormulaRepr (flatClauseToFormula, implClauseToFormula)

formula :: Form
formula = Atom "a" :=>: (Atom "b" :=>: Atom "c")

(flat, impl) = C.clausify [formula]
flatFormulae = map flatClauseToFormula flat
implFormulae = map implClauseToFormula impl

main :: IO ()
main = do
  print flatFormulae
  print implFormulae
