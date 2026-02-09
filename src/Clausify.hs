module Clausify (clausify) where

import Data.Set(Set)

import qualified Data.Set as Set
import qualified Data.Bifunctor as Bifunctor

import qualified Internal.Clausify as IC
import qualified Internal.FormulaRepr as IFR

import Formula (Formula, implication, variable)

clausify :: Formula -> (Set Formula, Set Formula, Formula)
clausify formula =
  (flats, impls, q)
  where
    b = implication formula q
    q = variable "$"

    (flats, impls) = Bifunctor.bimap
                     (Set.fromList . map IFR.flatClauseToFormula)
                     (Set.fromList . map IFR.implClauseToFormula)
                     (IC.clausify [IFR.formulaToForm b])
