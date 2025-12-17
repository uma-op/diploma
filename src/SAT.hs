{-# LANGUAGE LambdaCase #-}

module SAT where

import qualified Data.Foldable as Foldable
import qualified Data.Map as Map
import Data.Map (Map, (!))
import qualified Data.Maybe as Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Traversable as Traversable
import Formula
import Z3.Monad
import Data.Either (Either(..))
import Data.Void (Void)


prove :: Set Formula -> Set Formula -> Formula -> IO Bool
prove impls flats atom = intuitProve sol impls Set.empty atom
  where
    clauses :: Set Formula
    clauses = Set.union flats (Set.map (\case (Implication [Implication [a, b], c]) -> (implication b c)) impls)

    sol :: Z3 (Map String AST)
    sol = newSolver >> Traversable.sequence (Map.fromSet mkFreshBoolVar $ Set.unions $ Set.map variables clauses)


intuitProve :: Z3 (Map String AST) -> Set Formula -> Set Formula -> Formula -> IO Bool
intuitProve sol impls adds atom = do
  proved <- satProve sol adds atom
  case proved of
    Left _ -> undefined
    Right model -> undefined


newSolver :: Z3 ()
newSolver = return ()

addClause :: Z3 (Map String AST) -> Formula -> Z3 (Map String AST)
addClause sol f = do
  vars <- sol
  createAssertion f vars
  return vars

satProve :: Z3 (Map String AST) -> Set Formula -> Formula -> IO (Either (Set Formula) (Map String Bool))
satProve sol additionalClauses atom = evalZ3 z3Script
  where
    z3Script :: Z3 (Either (Set Formula) (Map String Bool))
    z3Script = do
      vars <- sol
      Foldable.foldr1 (>>) $ map (`createAssertion` vars) $ Set.toList additionalClauses
      createAssertion (negation atom) vars
      
      (result, model) <- withModel $ \m -> Map.map Maybe.fromJust <$> mapM (evalBool m) vars
      case result of
        Sat -> return $ Right (Maybe.fromJust model)
        Unsat -> return $ Left (Set.empty)
        Undef -> undefined

