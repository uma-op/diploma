module Refactoring.Prover.CArrow(module Refactoring.Prover.CArrow) where

import Control.Applicative
import qualified Data.Set as Set
import qualified Data.List as List
import Data.Bifunctor

import Refactoring.Formula.Atom
import Refactoring.Clause.Impl
import Refactoring.Sequent.Intuit
import Refactoring.Sequent.Classic
import Refactoring.Prover.LJT
import Refactoring.Prover.CounterModel
import Refactoring.Prover.Solver
import Refactoring.Sequent.Annotated
import Refactoring.Clause.Flat

import Z3.Base
import Fmt

data CArrowRule_ a c =
  CPL0 (Intuit_ a c) (Classic_ a c) |
  CPL1 (Intuit_ a c) (Classic_ a c) (CArrowRule_ a c) (Flat_ c) (Impl_ c) |

  ExCPL0 (Intuit_ a c) (LJTRule_ a c) |
  ExCPL1 (Intuit_ a c) (LJTRule_ a c) (CArrowRule_ a c) (Flat_ c) (Impl_ c)

rootCArrow :: CArrowRule_ a c -> Intuit_ a c
rootCArrow (CPL0 iseq _) = iseq
rootCArrow (CPL1 iseq _ _ _ _) = iseq
rootCArrow (ExCPL0 iseq _) = iseq
rootCArrow (ExCPL1 iseq _ _ _ _) = iseq

instance Functor (CArrowRule_ a) where
  fmap f (CPL0 iseq cseq) = CPL0 (second f iseq) (second f cseq)
  fmap f (CPL1 iseq cseq r newFlat learnedImpl) = CPL1 (second f iseq) (second f cseq) (fmap f r) (f <$> newFlat) (f <$> learnedImpl)
  fmap f (ExCPL0 iseq r) = ExCPL0 (second f iseq) (second f r)
  fmap f (ExCPL1 iseq ljtRule rule newFlat learnedImpl) = ExCPL1 (second f iseq) (second f ljtRule) (second f rule) (f <$> newFlat) (f <$> learnedImpl)

instance Bifunctor CArrowRule_ where
  first f (CPL0 iseq cseq) = CPL0 (first f iseq) (first f cseq)
  first f (CPL1 iseq cseq r newFlat learnedImpl) = CPL1 (first f iseq) (first f cseq) (first f r) newFlat learnedImpl
  first f (ExCPL0 iseq ljtRule) = ExCPL0 (first f iseq) (first f ljtRule)
  first f (ExCPL1 iseq ljtRule rule newFlat learnedImpl) = ExCPL1 (first f iseq) (first f ljtRule) (first f rule) newFlat learnedImpl

  second = fmap

instance (BuildableAnnotation a, BuildableAnnotation c) => Buildable (CArrowRule_ a c) where
  build (CPL0 iseq cseq) = "Intuit[" +| iseq |+ "] Classic[" +| cseq |+ "]"
  build (CPL1 iseq cseq rule _ _) = "Intuit[" +| iseq |+ "] Classic[" +| cseq |+ "]\n" +| rule |+ ""
  build (ExCPL0 iseq ljtRule) = undefined
  build (ExCPL1 iseq ljtRule rule _ _) = undefined

carrow :: Intuit_ () AST -> Solver_ -> IO (Either (CounterModel_ AST) (CArrowRule_ () AST))
carrow iseq@(Intuit flats impls goal) solver = do
  result <- satProve solver [] goal
  case result of
    Yes _ -> return $ Right $ CPL0 iseq (Classic flats [] goal)
    No model -> do
      result <- innerLoop iseq (newCounterModel model) solver
      case result of 
        Left counterModel -> return $ Left counterModel
        Right (assumptions, learnedClause) -> do
          let (Impl a b c) = learnedClause
          let classicSequent = Classic flats (addAnnotation () <$> a : assumptions) (addAnnotation () b)
          let newClause = Flat (List.delete a assumptions) [c]
          addClause solver newClause

          let intuitSequent = Intuit (Annotated () newClause : flats) impls goal
          result <- carrow intuitSequent solver

          case result of  
            Left counterModel -> return $ Left counterModel
            Right proof -> return $ Right $ CPL1 iseq classicSequent proof newClause learnedClause

innerLoop ::
  Intuit_ () AST ->
  CounterModel_ AST ->
  Solver_ ->
  IO (Either (CounterModel_ AST) ([Annotated_ AST Atom_], Impl_ AST))
innerLoop iseq@(Intuit flats impls goal) counterModel solver = do
  let selectedWorld = asum [do sw <- selectWorld counterModel i; return (i, sw) | (Annotated () i) <- impls] 
  case selectedWorld of 
    Just (learned@(Impl a b c), (World worldId as)) -> do
      result <- satProve solver (Set.toList $ Set.insert a as) (addAnnotation () b)
      case result of
        Yes core -> return $ Right (core, learned)
        No model -> innerLoop iseq (addWorld counterModel worldId model) solver
    Nothing -> return $ Left counterModel

extendProof :: CArrowRule_ () () -> CArrowRule_ () ()
extendProof (CPL0 iseq cseq) = ExCPL0 iseq (ljt cseq)
extendProof (CPL1 iseq cseq rule newFlat learnedImpl) = ExCPL1 iseq (ljt cseq) (extendProof rule) newFlat learnedImpl
extendProof _ = undefined
