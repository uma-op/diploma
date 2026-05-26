{-# LANGUAGE GADTs #-}

module Clausify where

import qualified Control.Monad as MD
import qualified Control.Monad.State as ST
import qualified Data.Bifunctor as BF
import qualified Data.Maybe as MB
import Formula
  ( Formula (..),
    asPair,
    conjunction,
    disjunction,
    implication,
    isAtom,
    top,
    variable,
  )

import qualified Clause
import qualified Z3.Base as Z3
import qualified Data.List as List

clausify :: Formula -> ([Clause.FlatClauseFormula], [Clause.ImplClauseFormula], Formula)
clausify formula =
  (flats, impls, q)
  where
    b = implication formula q
    q = variable "$"

    ((flats, impls), _) = ST.runState (clausifyLoopS [] [] [b]) 0

    clausifyS :: Formula -> ST.State Int [Formula]
    clausifyS (Implication [Disjunction ds, v@(Variable _)]) = return $ map (`implication` v) ds
    clausifyS (Implication [v@(Variable _), Conjunction cs]) = return $ map (implication v) cs
    clausifyS (Implication (x : y : z : is)) = return [Implication (conjunction x y : z : is)]
    clausifyS (Implication [x, Disjunction ds]) = do
      aliases <- MD.mapM (aliasS False) ds
      let (newDs, additional) = BF.second MB.catMaybes $ unzip aliases
      return (implication x (foldr1 disjunction newDs) : additional)
    clausifyS i@(Implication (Conjunction cs : is)) = do
      let (_, rhs) = asPair i
      aliases <- MD.mapM (aliasS True) cs
      let (newCs, additional) = BF.second MB.catMaybes $ unzip aliases
      return (implication (foldr1 conjunction newCs) rhs : additional)
    clausifyS i1@(Implication (i2@(Implication (x: is1)) : is2)) = do
      let (_, rhs1) = asPair i1
      let (_, rhs2) = asPair i2
      (aliasX, correspondanceX) <- aliasS False x
      (aliasY, correspondanceY) <- aliasS True rhs1
      (aliasZ, correspondanceZ) <- aliasS False rhs2
      return (implication (implication aliasX aliasY) aliasZ : MB.catMaybes [correspondanceX, correspondanceY, correspondanceZ])
    clausifyS x = return [implication top x]

    aliasS :: Bool -> Formula -> ST.State Int (Formula, Maybe Formula)
    aliasS isReversed f
      | isAtom f = return (f, Nothing)
      | otherwise = do
          freshVariable <- freshS
          return
            ( freshVariable,
              Just
                ( if isReversed
                    then implication f freshVariable
                    else implication freshVariable f
                )
            )

    freshS :: ST.State Int Formula
    freshS = ST.state (\s -> (Variable $ show s, s + 1))

    clausifyLoopS ::
      [Clause.FlatClauseFormula] ->
      [Clause.ImplClauseFormula] ->
      [Formula] ->
      ST.State Int ([Clause.FlatClauseFormula], [Clause.ImplClauseFormula])

    clausifyLoopS f i (nph : npt) = do
      case Clause.flatClauseFromFormula nph of
        Just clause -> clausifyLoopS (clause:f) i npt
        Nothing -> case Clause.implClauseFromFormula nph of
                      Just clause -> clausifyLoopS f (clause:i) npt
                      Nothing -> do
                        clausified <- clausifyS nph
                        clausifyLoopS f i (clausified ++ npt)

    clausifyLoopS f i [] = return (f, i)


createAssertion :: (Formula -> Z3.AST) -> Z3.Context -> Formula -> IO Z3.AST
createAssertion vs ctx = createZ3Formula
  where
    createZ3Formula :: Formula -> IO Z3.AST
    createZ3Formula (Implication fs) = List.foldr1 foldingFunction z3Formulae
      where
        z3Formulae = map createZ3Formula fs

        foldingFunction :: IO Z3.AST -> IO Z3.AST -> IO Z3.AST
        foldingFunction lhs rhs = do x <- lhs; y <- rhs; Z3.mkImplies ctx x y
    createZ3Formula (Conjunction fs) = sequence z3Formulae >>= Z3.mkAnd ctx
      where
        z3Formulae = map createZ3Formula fs
    createZ3Formula (Disjunction fs) = sequence z3Formulae >>= Z3.mkOr ctx
      where
        z3Formulae = map createZ3Formula fs
    createZ3Formula v@(Variable _) = return $ vs v

newtype FlatClauseAST = FlatClauseAST {
  flatClauseAST :: Z3.AST
}

data ImplClauseAST = ImplClauseAST {
  implClauseAST :: Z3.AST,
  aImpliesBAST :: Z3.AST,
  aAST :: Z3.AST,
  bAST :: Z3.AST,
  cAST :: Z3.AST
}

flatToAST :: (Formula -> Z3.AST) -> Z3.Context -> Clause.FlatClauseFormula -> IO FlatClauseAST
flatToAST varToAST context flat@(Clause.FlatClauseFormula cfs dfs) = do
  let csAST = map varToAST cfs
  let dsAST = map varToAST dfs

  cAST <- Z3.mkAnd context csAST
  dAST <- Z3.mkOr context dsAST

  clauseAST <- Z3.mkImplies context cAST dAST
  return FlatClauseAST {
    flatClauseAST = clauseAST
  }

implToAST :: (Formula -> Z3.AST) -> Z3.Context -> Clause.ImplClauseFormula -> IO ImplClauseAST
implToAST varToAST context impl@(Clause.ImplClauseFormula af bf cf) = do
  let aAST = varToAST af 
  let bAST = varToAST bf 
  let cAST = varToAST cf 

  lhsAST <- Z3.mkImplies context aAST bAST
  clauseAST <- Z3.mkImplies context lhsAST cAST

  return ImplClauseAST {
    implClauseAST = clauseAST,
    aImpliesBAST = lhsAST,
    aAST = aAST,
    bAST = bAST,
    cAST = cAST
  }

