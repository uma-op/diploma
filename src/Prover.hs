{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module Prover(prove, ProvingResult(..)) where

import Debug.Trace

import qualified Data.Foldable as Foldable
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import qualified Data.Traversable as Traversable

import Data.Map (Map)
import Data.Set (Set)

import Control.Monad (unless)

import Formula
import Z3.Monad
    ( AST,
      Result(Undef, Unsat, Sat),
      evalBool,
      evalZ3,
      mkFreshBoolVar,
      withModel,
      Z3 )
import Clausify (clausify)


badImplicationClauseError :: a
badImplicationClauseError = error "Bad implication clause"

data ProvingResult where
  Yes :: (Set Formula) -> ProvingResult
  No :: (Set Formula) -> ProvingResult

deriving instance Show ProvingResult
deriving instance Eq ProvingResult

prove :: Formula -> IO ProvingResult
prove formula = trace ("prove: formula = [" ++ show formula ++ "]") $ intuitProve sol impls Set.empty atom
  where
    (flats, impls, atom) = traceShowId $ clausify formula
    
    clauses :: Set Formula
    clauses = Set.union flats (Set.map implCast impls)
      where
        implCast clause@(Implication [Implication [a, b], c]) = implication b c
        implCast _ = badImplicationClauseError

    sol :: Z3 (Map String AST)
    sol = do
      newSolver
      vars <- Traversable.sequence (Map.fromSet mkFreshBoolVar
                            $ Set.unions
                            $ Set.map variables
                            $ Set.unions [flats, impls, Set.singleton atom]
                           )
      Foldable.foldr1 (>>) $ map (`createAssertion` vars) $ Set.toList clauses
      return vars
      
          
intuitProve :: Z3 (Map String AST) -> Set Formula -> Set Formula -> Formula -> IO ProvingResult
intuitProve sol impls adds atom = trace ("intuitProve: impls = [" ++ show impls ++ "] adds = [" ++ show adds ++ "] atom = [" ++ show atom ++ "]") $ do
  proved <- satProve sol adds atom
  case proved of
    Yes formulae -> return proved
    No model -> do check <- intuitCheck sol impls model
                   case check of
                     Nothing -> return $ No model
                     Just newSol -> intuitProve newSol impls adds atom


-- Returns Nothing if can't be proved for all impls
-- otherwise returns Just of solver with new clause /\(A_1 \ {a}) -> c
intuitCheck :: Z3 (Map String AST) -> Set Formula -> Set Formula -> IO (Maybe (Z3 (Map String AST)))
intuitCheck sol impls model = trace ("intuitCheck: impls = [" ++ show impls ++ "] model = [" ++ show model ++ "]") $ intuitCheck' sol implsToTraverse
  where
    implsFilter (Implication [Implication [a, b], c]) = not $ Foldable.any (`Set.member` model) [a, b, c]
    implsFilter _ = badImplicationClauseError
    
    implsToTraverse = Set.filter implsFilter impls

    cycle i@(Implication [Implication [a, b], c]) = do
      proved <- intuitProve sol (Set.delete i impls) (Set.insert a model) b
      case proved of
        Yes formulae -> do
          let formulaeWithoutAtom = Set.delete a formulae
          if Set.null formulaeWithoutAtom
            then return $ Just $ addClause sol c
            else return $ Just $ addClause sol (implication (Foldable.foldr1 conjunction formulaeWithoutAtom) c)
        No model -> return Nothing
    cycle _ = badImplicationClauseError

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
addClause sol f = trace ("addClause: f = [" ++ show f ++ "]") $ do
  vars <- sol
  createAssertion f vars
  return vars

satProve :: Z3 (Map String AST) -> Set Formula -> Formula -> IO ProvingResult
satProve sol additionalClauses atom = trace ("satProve: A = [" ++ show additionalClauses ++ "] q = [" ++ show atom ++ "]") $  evalZ3 z3Script
  where
    z3Script = do
      vars <- sol

      unless
        (Set.null additionalClauses)
        (Foldable.foldr1 (>>) $ map (`createAssertion` vars) $ Set.toList additionalClauses)
        
      createAssertion (negation atom) vars
      
      (result, model) <- withModel $ \m -> Map.map Maybe.fromJust <$> mapM (evalBool m) vars
      case result of
        Unsat -> return $ traceShowId $ Yes additionalClauses
        Sat -> (return . traceShowId . No . Set.map variable . Map.keysSet . Map.filter id . Maybe.fromJust) model
        Undef -> undefined

