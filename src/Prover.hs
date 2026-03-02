{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module Prover(prove, ProvingResult(..)) where

import qualified Data.Foldable as Foldable
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import qualified Data.Traversable as Traversable

import Data.Map (Map)
import Data.Set (Set)
import Data.Functor ((<&>))

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

import qualified KripkeModel
import Debug.Trace (traceShowId, trace)

badImplicationClauseError :: a
badImplicationClauseError = error "Bad implication clause"

data ProvingResult where
  Yes :: (Set Formula) -> ProvingResult
  No :: (Set Formula) -> ProvingResult

deriving instance Show ProvingResult
deriving instance Eq ProvingResult

data SatContext a where
  SatContext :: { satBase :: Z3 (Map String AST)
                , satAssertions :: [Formula]
                , satCounterModel :: KripkeModel
                , satStorage :: a
                } -> SatContext a

instance Show a => Show (SatContext a) where
  show ctx = "[assertions: " ++ show (satAssertions ctx)
           ++ "] [storage: " ++ show (satStorage ctx)
           ++ "] [counter model: " ++ show (satCounterModel ctx)

prove :: Formula -> IO ProvingResult
prove formula = intuitProve impls Set.empty atom (SatContext sol clauses KripkeModel.empty ()) <&> (satStorage . traceShowId)
  where
    (flats, impls, atom) = clausify formula
    
    clauses :: [Formula]
    clauses = Set.toList $ Set.union flats (Set.map implCast impls)
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
      Foldable.foldr1 (>>) $ map (`createAssertion` vars) clauses
      return vars
      
          
intuitProve :: Set Formula -> Set Formula -> Formula -> SatContext a -> IO (SatContext ProvingResult)
intuitProve impls adds atom ctx =
  do
    newCtx <- satProve adds atom ctx
    case satStorage newCtx of
      Yes formulae -> return newCtx
      No model -> do checkCtx <- intuitCheck impls model ctx
                     if satStorage checkCtx then
                       return $ checkCtx { satStorage = No model }
                     else
                       intuitProve impls adds atom checkCtx

intuitCheck :: Set Formula -> Set Formula -> SatContext a -> IO (SatContext Bool)
intuitCheck impls model ctx = trace (show model) $
  intuitCheck' implsToTraverse ctx
  where
    implsFilter (Implication [Implication [a, b], c]) = not $ Foldable.any (`Set.member` model) [a, b, c]
    implsFilter _ = badImplicationClauseError
    
    implsToTraverse = Set.filter implsFilter impls

    cycle :: Formula -> SatContext a -> IO (SatContext ProvingResult)
    cycle i@(Implication [Implication [a, b], c]) ctx = do
      proved <- intuitProve (Set.delete i impls) (Set.insert a model) b ctx
      case satStorage proved of
        Yes formulae -> do
          let formulaeWithoutAtom = Set.delete a formulae
          if Set.null formulaeWithoutAtom
            then return $ addClause c proved 
            else return $ addClause (implication (Foldable.foldr1 conjunction formulaeWithoutAtom) c) proved
        No model -> return proved
    cycle _ _ = badImplicationClauseError

    intuitCheck' :: Set Formula -> SatContext a -> IO (SatContext Bool)
    intuitCheck' impls ctx = if Set.null impls
                               then return $ ctx { satStorage = True
                                                 , satCounterModel = KripkeModel.setValuation
                                                                       (satCounterModel ctx)
                                                                       (map (\(Variable v) -> v) $ Set.toList model)
                                                 }
                               else do let (himpls, timpls) = Set.deleteFindMin impls
                                       result <- cycle himpls ctx
                                       case satStorage result of
                                         Yes _ -> return $ result { satStorage = False }
                                         No _ -> intuitCheck' timpls $ result { satCounterModel = KripkeModel.addWorld
                                                                                                    (satCounterModel ctx)
                                                                                                    (satCounterModel result)
                                                                              }


newSolver :: Z3 ()
newSolver = return ()

addClause :: Formula -> SatContext a -> SatContext a
addClause f ctx =
  ctx { satBase = do vars <- satBase ctx
                     createAssertion f vars
                     return vars
      , satAssertions = f : satAssertions ctx
      }

satProve :: Set Formula -> Formula -> SatContext a -> IO (SatContext ProvingResult)
satProve additionalClauses atom ctx =
  evalZ3 z3Script
  where
    z3Script = do
      vars <- satBase ctx

      unless
        (Set.null additionalClauses)
        (Foldable.foldr1 (>>) $ map (`createAssertion` vars) $ Set.toList additionalClauses)
        
      createAssertion (negation atom) vars
      
      (result, model) <- withModel $ \m -> Map.map Maybe.fromJust <$> mapM (evalBool m) vars
      case result of
        Unsat -> return $ ctx { satStorage = Yes additionalClauses }
        Sat -> return $ ctx { satStorage = (No . Set.map variable . Map.keysSet . Map.filter id . Maybe.fromJust) model }
        Undef -> undefined

