module Clausify (clausify) where

import Data.Set(Set)

import qualified Data.Set as Set
import qualified Data.Bifunctor as Bifunctor

import qualified Internal.Clausify as IC
import qualified Internal.FormulaRepr as IFR

import Formula (Formula, implication, variable)

clausify :: Formula -> ([Formula], [Formula], Formula)
clausify formula =
  (flats, impls, q)
  where
    toClausify = implication b q
    b = implication formula q
    q = variable "$"

    (flats, impls) = Bifunctor.bimap
                     (map IFR.flatClauseToFormula)
                     (map IFR.implClauseToFormula)
                     (IC.clausify [IFR.formulaToForm toClausify])
