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
import Control.Monad(unless)


prove :: Set Formula -> Set Formula -> Formula -> IO (Either (Set Formula) (Set Formula))
prove impls flats = intuitProve sol impls Set.empty
  where
    clauses :: Set Formula
    clauses = Set.union flats (Set.map (\case (Implication [Implication [a, b], c]) -> (implication b c)) impls)

    sol :: Z3 (Map String AST)
    sol = newSolver >> Traversable.sequence (Map.fromSet mkFreshBoolVar $ Set.unions $ Set.map variables clauses)
-- Left means that formula is derivable
-- Right means that formula does not derivable

-- Left means that formula is derivable
-- Right means that formula does not derivable
intuitProve :: Z3 (Map String AST) -> Set Formula -> Set Formula -> Formula -> IO (Either (Set Formula) (Set Formula))
intuitProve sol impls adds atom = do
  proved <- satProve sol adds atom
  case proved of
    Left formulae -> return proved
    Right model -> do check <- intuitCheck sol impls model
                      case check of
                        Nothing -> return $ Right model
                        Just newSol -> intuitProve newSol impls adds atom


-- Returns Nothing if can't be proved for all impls
-- otherwise returns Just of solver with new clause /\(A_1 \ {a}) -> c
intuitCheck :: Z3 (Map String AST) -> Set Formula -> Set Formula -> IO (Maybe (Z3 (Map String AST)))
intuitCheck sol impls model = intuitCheck' sol implsToTraverse
  where
    implsFilter (Implication [Implication [a, b], c]) = not $ Foldable.any (`Set.member` model) [a, b, c]    
    implsToTraverse = Set.filter implsFilter impls

    cycle i@(Implication [Implication [a, b], c]) = do
      proved <- intuitProve sol (Set.delete i impls) (Set.insert a model) b
      case proved of
        Left formulae -> return $ Just $ addClause sol (implication (Foldable.foldr1 conjunction formulae) c)
        Right model -> return Nothing

    intuitCheck' sol impls = if Set.null impls
                               then return Nothing
                               else do let (himpls, timpls) = Set.deleteFindMin impls
                                       result <- cycle himpls
                                       case result of
                                         Just newSol -> return result
                                         Nothing -> intuitCheck' sol timpls


newSolver :: Z3 ()
newSolver = return ()

addClause :: Z3 (Map String AST) -> Formula -> Z3 (Map String AST)
addClause sol f = do
  vars <- sol
  createAssertion f vars
  return vars

-- Left means that atom is dirivable from argument of sol and additionalClauses (TODO: return minimal subset from premises)
-- Right means that atom does not derivable, right's set is counter-model
satProve :: Z3 (Map String AST) -> Set Formula -> Formula -> IO (Either (Set Formula) (Set Formula))
satProve sol additionalClauses atom = evalZ3 z3Script
  where
    z3Script = do
      vars <- sol

      unless
        (Set.null additionalClauses)
        (Foldable.foldr1 (>>) $ map (`createAssertion` vars) $ Set.toList additionalClauses)
        
      createAssertion (negation atom) vars
      
      (result, model) <- withModel $ \m -> Map.map Maybe.fromJust <$> mapM (evalBool m) vars
      case result of
        Unsat -> return $ Left additionalClauses
        Sat -> (return . Right . Set.map variable . Map.keysSet . Map.filter id . Maybe.fromJust) model
        Undef -> undefined

