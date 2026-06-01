{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}

module ProverR where

import qualified Data.Tuple as Tuple
import Clausify
import qualified Data.Set as Set
import Data.Map (Map, (!))
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Maybe as Maybe

import Formula
import Sequent
import Clause

import World (World(..))
import qualified World
import CounterModel (CounterModel, newCounterModel)
import qualified CounterModel
import Proof

import qualified IncrementalSolver

import qualified Z3.Base as Z3

data ValidationResult where
  Valid :: ([(PlainSequent, PlainSequent, CArrowRule)], [(PlainSequent, ClausificationRule)]) -> ValidationResult
  Invalid :: CounterModel -> ValidationResult

proveR :: Z3.Context -> Z3.Solver -> PlainFormula -> IO ValidationResult
proveR context solver f = do
  let (IntuitPlainSequent flats impls goal, history) = clausify f

  putStrLn $ unlines $ map (\(seq, rule) -> plainSequentToString seq ++ " by " ++ show rule) history

  let vars = Set.unions (Set.singleton goal : map atoms flats ++ map atoms impls)

  varToASTMap <- sequence $ Map.fromSet (Formula.atomToAST context) vars
  let varToAST = (!) varToASTMap

  let astToVarMap = Map.fromList $ map Tuple.swap $ Map.toList varToASTMap
  let astToVar = (!) astToVarMap

  funcDeclToASTMap <-
    Map.fromList <$>
    mapM (\ast -> (,ast) <$> (Z3.getAppDecl context =<< Z3.toApp context ast))
    (Map.elems varToASTMap)

  let funcDeclToAST = (!) funcDeclToASTMap

  let flatsAST = map (fmap varToAST) flats
  let implsAST = map (fmap varToAST) impls
  let goalAST = varToAST goal

  IncrementalSolver.initSolver context solver flatsAST

  let
    proveR'' :: [ImplClauseFormula Z3.AST] -> CounterModel -> IO (Either ([Z3.AST], ImplClauseFormula Z3.AST) CounterModel)
    proveR'' impls counterModel = do
      -- putStrLn . ("Selecting in counter model: " ++ ) =<< CounterModel.counterModelToString context counterModel
      let maybeWorldAndClause = Maybe.catMaybes [uncurry (,,impl) <$> CounterModel.selectWorld counterModel impl | impl <- impls]
      case maybeWorldAndClause of 
        ((worldId, world, c):_) -> do
          -- putStrLn "proveR'':"
          -- putStrLn . ("Returned world: " ++) =<< World.worldAsString context world
          -- putStrLn . ("Found Clause: " ++) =<< Z3.astToString context (implClauseAST c)
          result <- IncrementalSolver.satProve funcDeclToAST context solver (a_ c : Set.toList (consts world)) (b_ c)
          case result of
            IncrementalSolver.Yes core -> do
              -- putStrLn "S5 Core"
              -- putStrLn . ("Core ASTs: " ++ ) . show =<< mapM (Z3.astToString context) core
              return $ Left (core, c)
            IncrementalSolver.No newWorld -> do
              -- putStrLn "S5 Model"
              -- putStrLn =<< World.worldAsString context newWorld
              proveR'' impls (CounterModel.addWorld counterModel worldId newWorld)

        [] -> return $ Right counterModel

    proveR' :: PlainSequent -> [(PlainSequent, PlainSequent, CArrowRule)] -> IO ValidationResult
    proveR' rootSeq@(IntuitPlainSequent r x g) plainDt = do
      result <- IncrementalSolver.satProve funcDeclToAST context solver [] goalAST
      case result of
        IncrementalSolver.Yes a -> return $ Valid ((rootSeq, ClassicPlainSequent r (map astToVar a) g, CPL0):plainDt, history)
        IncrementalSolver.No m -> do
          -- putStrLn "S2 Model"
          -- putStrLn =<< World.worldAsString context m

          result <- proveR'' implsAST (CounterModel.newCounterModel m)
          case result of
            Left (assumptions, impl) -> do
              let newClause = FlatClauseFormula (List.delete (a_ impl) assumptions) [c_ impl]
                    (Implication [
                      Conjunction $ Atom . astToVar <$> List.delete (a_ impl) assumptions,
                      Atom . astToVar $ c_ impl
                    ])
              let newClauseFormula = astToVar <$> newClause
              let learnedClauseFormula = astToVar <$> impl
              IncrementalSolver.addClause context solver newClause
              proveR'
                (IntuitPlainSequent (newClauseFormula:r) x g)
                ((rootSeq, ClassicPlainSequent r (map astToVar assumptions) (astToVar $ b_ impl), CPL1 newClauseFormula learnedClauseFormula):plainDt)
            Right counterModel -> return $ Invalid counterModel
    proveR' _ _ = undefined
    in proveR' (IntuitPlainSequent flats impls goal) []

