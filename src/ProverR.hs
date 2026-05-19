{-# LANGUAGE GADTs #-}

module ProverR where

import Clausify
import qualified Data.Foldable as Foldable
import qualified Data.Set as Set
import Formula
import IncrementalSolver

data ValidationResult where
  Valid :: ValidationResult

proveR :: Formula -> IO ValidationResult
proveR f = undefined
  where
    (_R, _X, g) = clausify f
    varNames =
      (Set.toList . Set.unions)
        ( variables g
            : ( map variables _R
                  ++ map variables _X
              )
        )
    s = Foldable.foldr addClause (newSolver varNames) (_R ++ [implication b c | (Implication [Implication [a, b], c]) <- _X])
