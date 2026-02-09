{-# LANGUAGE LambdaCase #-}
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

import Debug.Trace


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
                , satStorage :: a
                } -> SatContext

prove :: Formula -> IO ProvingResult
prove formula = intuitProve sol impls Set.empty atom
  where
    (flats, impls, atom) = clausify formula
    
    clauses :: [Formula]
    clauses = Set.toList $ Set.union flats (Set.map implCast impls)
      where
        implCast clause@(Implication [Implication [a, b], c]) = implication b c
        implCast _ = badImplicationClauseError

    sol :: Z3 SatContext
    sol = do
      newSolver
      vars <- Traversable.sequence (Map.fromSet mkFreshBoolVar
                            $ Set.unions
                            $ Set.map variables
                            $ Set.unions [flats, impls, Set.singleton atom]
                           )
      Foldable.foldr1 (>>) $ map (`createAssertion` vars) clauses
      return $ SatContext vars clauses
      
          
intuitProve :: Set Formula -> Set Formula -> Formula -> SatContext a -> SatContext (IO ProvingResult)
intuitProve impls adds atom ctx = trace ("\nintuitProve: [impls: " ++ show impls ++ "] [adds: " ++ show adds ++ "] [atom: " ++ show atom ++ "]") $ do
  let newCtx = satProve adds atom ctx
  case satStorage newCtx of
    Yes formulae -> return proved
    No model -> do (check, newSol) <- intuitCheck sol impls model
                   if check then return ()

-- Returns Nothing if can't be proved for all impls
-- otherwise returns Just of solver with new clause /\(A_1 \ {a}) -> c
intuitCheck :: Set Formula -> Set Formula -> SatContext a -> SatContext (IO Bool)
intuitCheck impls model ctx = trace ("\nintuitCheck: [impls: " ++ show impls ++ "] [model: " ++ show model ++ "]") $ intuitCheck' sol implsToTraverse
  where
    implsFilter (Implication [Implication [a, b], c]) = not $ Foldable.any (`Set.member` model) [a, b, c]
    implsFilter _ = badImplicationClauseError
    
    implsToTraverse = Set.filter implsFilter impls

    cycle i@(Implication [Implication [a, b], c]) ctx = do
      proved <- intuitProve sol (Set.delete i impls) (Set. insert a model) b
      case proved of
        Yes formulae -> do
          let formulaeWithoutAtom = Set.delete a formulae
          if Set.null formulaeWithoutAtom
            then return $ Just $ addClause sol c
            else return $ Just $ addClause sol (implication (Foldable.foldr1 conjunction formulaeWithoutAtom) c)
        No model -> return Nothing
    cycle _ = badImplicationClauseError

    intuitCheck' impls ctx = if Set.null impls
                               then return Nothing
                               else do let (himpls, timpls) = Set.deleteFindMin impls
                                       result <- cycle himpls ctx
                                       case result of
                                         Just newSol -> return result
                                         Nothing -> intuitCheck' sol timpls


newSolver :: Z3 ()
newSolver = return ()

addClause :: Formula -> SatContext a -> SatContext a
addClause f ctx = trace ("addClause: [formula: " ++ show f ++ "]") $
  SatContext { satBase = do
                 vars <- satBase ctx
                 createAssertion f vars
                 return vars
             , satAssertions = f:(satAssertions ctx)
             }

satProve :: Set Formula -> Formula -> SatContext a -> SatContext (IO ProvingResult)
satProve additionalClauses atom ctx = trace ("\nsatProve: [additionalClauses: " ++ show additionalClauses ++ "] [atom: " ++ show atom ++ "]") $ ctx { satStorage = evalZ3 z3Script }
  where
    z3Script = do
      vars <- satBase ctx

      trace ("assertions: " ++ show (satAssertions ctx)) $ return ()
      
      unless
        (Set.null additionalClauses)
        (Foldable.foldr1 (>>) $ map (`createAssertion` vars) $ Set.toList additionalClauses)
        
      createAssertion (negation atom) vars
      
      (result, model) <- withModel $ \m -> Map.map Maybe.fromJust <$> mapM (evalBool m) vars
      trace ("satProve -> " ++ show result ++ " " ++ show model) $ return ()
      case result of
        Unsat -> return $ Yes additionalClauses
        Sat -> (return . No . Set.map variable . Map.keysSet . Map.filter id . Maybe.fromJust) model
        Undef -> undefined

