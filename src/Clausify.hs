{-# LANGUAGE GADTs #-}

module Clausify (clausify) where

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
    isFlatClause,
    isImplClause,
    top,
    variable,
  )

clausify :: Formula -> ([Formula], [Formula], Formula)
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

    clausifyLoopS :: [Formula] -> [Formula] -> [Formula] -> ST.State Int ([Formula], [Formula])
    clausifyLoopS f i (nph : npt)
      | isFlatClause nph = clausifyLoopS (nph : f) i npt
      | isImplClause nph = clausifyLoopS f (nph : i) npt
      | otherwise = do
          clausified <- clausifyS nph
          clausifyLoopS f i (clausified ++ npt)
    clausifyLoopS f i [] = return (f, i)
