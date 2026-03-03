{-# LANGUAGE GADTs #-}

module IncrementalSolver ( IncrementalSolver
                         , newSolver
                         , addClause
                         , ProvingResult(..)
                         , satProve
                         ) where

import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Foldable as Foldable
import qualified Data.Maybe as Maybe

import qualified Data.Traversable as Traversable

import Z3.Monad (Z3, mkFreshBoolVar, evalZ3, withModel, evalBool, Result(..))
import Formula (Formula, createAssertion, Variables(..), negation, variable)
import Control.Monad (unless)

data IncrementalSolver = IncrementalSolver { solver :: Z3 Variables
                                           , formulas :: [Formula] }

newSolver :: [String] -> IncrementalSolver
newSolver names = IncrementalSolver { solver = Variables . Map.fromList . zip names <$>
                                               Traversable.traverse mkFreshBoolVar names
                                    , formulas = []
                                    }

addClause :: Formula -> IncrementalSolver -> IncrementalSolver 
addClause f s = IncrementalSolver {solver = do
                                    vars <- solver s
                                    createAssertion f vars
                                    return vars
                                  , formulas=f:formulas s}


data ProvingResult where
  Yes :: [Formula] -> ProvingResult
  No :: [Formula] -> ProvingResult

satProve :: [Formula] -> Formula -> IncrementalSolver -> IO ProvingResult
satProve adds atom s = evalZ3 $ do
  vars@(Variables varsData) <- solver s
  unless (List.null adds)
         (Foldable.foldr1 (>>) $ map (`createAssertion` vars) adds)
  createAssertion (negation atom) vars
  (result, model) <- withModel $ \m -> Map.map Maybe.fromJust <$> mapM (evalBool m) varsData

  case result of
    Unsat -> return $ Yes adds
    Sat -> return $ No $ [variable name | (name, value) <- (Map.toList . Maybe.fromJust) model, value]
    Undef -> undefined
