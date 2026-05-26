{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}

module ProverR where

import Clausify
import qualified Data.Set as Set
import Data.Map (Map, (!))
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Maybe as Maybe

import qualified Clause

import Formula (Formula)
import qualified Formula
import World (World(..))
import qualified World
import CounterModel (CounterModel, newCounterModel)
import qualified CounterModel

import IncrementalSolver (IncrementalSolver (..))
import qualified IncrementalSolver

import qualified Z3.Base as Z3

data ValidationResult where
  Valid :: ValidationResult
  Invalid :: CounterModel -> ValidationResult

proveR :: Z3.Context -> Z3.Solver -> Formula -> IO ValidationResult
proveR context solver f = do
  let (flats, impls, goal) = clausify f

  putStrLn "Clausified"
  putStrLn ("R: " ++ show flats)
  putStrLn ("X: " ++ show impls)
  putStrLn ("g: " ++ show goal)

  let vars = Set.unions (Set.singleton goal : map Clause.variables flats ++ map Clause.variables impls)

  varToASTMap <- sequence $ Map.fromSet (Formula.atomToAST context) vars
  let varToAST = (!) varToASTMap

  funcDeclToASTMap <-
    Map.fromList <$>
    mapM (\ast -> (,ast) <$> (Z3.getAppDecl context =<< Z3.toApp context ast))
    (Map.elems varToASTMap)

  let funcDeclToAST = (!) funcDeclToASTMap

  flatsAST <- mapM (Clausify.flatToAST varToAST context) flats
  implsAST <- mapM (Clausify.implToAST varToAST context) impls
  let goalAST = varToAST goal

  IncrementalSolver.initSolver context solver flatsAST

  let
    proveR'' :: [Clausify.ImplClauseAST] -> CounterModel -> IO (Either ([Z3.AST], Clausify.ImplClauseAST) CounterModel)
    proveR'' impls counterModel = do
      putStrLn . ("Selecting in counter model: " ++ ) =<< CounterModel.counterModelToString context counterModel
      let maybeWorldAndClause = Maybe.catMaybes [uncurry (,,impl) <$> CounterModel.selectWorld counterModel impl | impl <- impls]
      case maybeWorldAndClause of 
        ((worldId, world, c):_) -> do
          putStrLn "proveR'':"
          putStrLn . ("Returned world: " ++) =<< World.worldAsString context world
          putStrLn . ("Found Clause: " ++) =<< Z3.astToString context (Clausify.implClauseAST c)
          result <- IncrementalSolver.satProve funcDeclToAST context solver (Clausify.aAST c : Set.toList (consts world)) (Clausify.bAST c)
          case result of
            IncrementalSolver.Yes core -> do
              putStrLn "S5 Core"
              putStrLn . ("Core ASTs: " ++ ) . show =<< mapM (Z3.astToString context) core
              return $ Left (core, c)
            IncrementalSolver.No newWorld -> do
              putStrLn "S5 Model"
              putStrLn =<< World.worldAsString context newWorld
              proveR'' impls (CounterModel.addWorld counterModel worldId newWorld)

        [] -> return $ Right counterModel

    proveR' :: IO ValidationResult
    proveR' = do
      result <- IncrementalSolver.satProve funcDeclToAST context solver [] goalAST
      case result of
        IncrementalSolver.Yes _ -> return Valid
        IncrementalSolver.No m -> do
          putStrLn "S2 Model"
          putStrLn =<< World.worldAsString context m

          result <- proveR'' implsAST (CounterModel.newCounterModel m)
          case result of
            Left (assumptions, impl) -> do
              newClauseAST <-
                flip (Z3.mkImplies context) (cAST impl) =<<
                Z3.mkAnd context (List.delete (aAST impl) assumptions)
              let newClause = Clausify.FlatClauseAST { Clausify.flatClauseAST = newClauseAST }
              IncrementalSolver.addClause context solver newClause
              proveR'
            Right counterModel -> return $ Invalid counterModel
    in proveR'

