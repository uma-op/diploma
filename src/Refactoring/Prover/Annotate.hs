module Refactoring.Prover.Annotate(module Refactoring.Prover.Annotate) where

import Control.Monad.State
import Data.Map (Map)

import Refactoring.Prover.Clausify
import Refactoring.Lambda.Lambda
import Refactoring.Prover.CArrow
import Refactoring.Prover.LJT
import Refactoring.Formula.Atom

data Environment = Environment Int (Map Atom_ Lambda_)

annotateClausification :: ClausificationRule_ () () -> State Int (ClausificationRule_ Lambda_ ())
annotateClausification = undefined

annotateCArrow :: CArrowRule_ () () -> State Int (CArrowRule_ Lambda_ ())
annotateCArrow = undefined

annotateLJT :: LJTRule_ () () -> State Int (LJTRule_ Lambda_ ())
annotateLJT () = undefined
