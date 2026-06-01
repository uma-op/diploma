{-# LANGUAGE GADTs #-}

module Clausify where

import qualified Control.Monad as MD
import qualified Control.Monad.State as ST
import qualified Data.Bifunctor as BF
import qualified Data.Maybe as MB
import qualified Z3.Base as Z3
import qualified Data.List as List

import Proof
import Formula
import Clause
import Sequent

import Debug.Trace

type ClausificationState = (Int, [(PlainSequent, ClausificationRule)])

clausify :: PlainFormula -> (PlainSequent, [(PlainSequent, ClausificationRule)])
clausify formula =
  (ext, history)
  where
    (initial, toGoalify) = ([], formula)


    b = implication toGoalify $ plain q
    q = atom $ variable "$"

    (seq, st) = ST.runState (clausifyLoopS (UnclausifiedPlainSequent [] [] (b:initial) q)) (0, [])
    (ext, (_, history)) = ST.runState (extendFlats seq) st

    extendFlats :: PlainSequent -> ST.State ClausificationState PlainSequent
    extendFlats pseq@(IntuitPlainSequent _ is _) = extendFlats' pseq is
      where
        extendFlats' :: PlainSequent -> [ImplClauseFormula Atom] -> ST.State ClausificationState PlainSequent
        extendFlats' pseq (h:t) = do
          extended <- extendFlat pseq h
          extendFlats' extended t
        extendFlats' pseq [] = return pseq

        extendFlat :: PlainSequent -> ImplClauseFormula Atom -> ST.State ClausificationState PlainSequent
        extendFlat pseq@(IntuitPlainSequent fs is g) ic = do
          let newFlatClause = implImpliesFlat ic
          putSequent (pseq, ImplImpliesFlat ic newFlatClause)
          let newSequent = pseq { plainFlats = newFlatClause : fs }
          return newSequent
        extendFlat _ _ = undefined
    extendFlats _ = undefined

    clausifyS :: PlainFormula -> ST.State ClausificationState ([PlainFormula], ClausificationRule)
    clausifyS f@(Implication [Disjunction ds, v]) = do
      let newFormulas = map (`implication` v) ds
      return (newFormulas, LeftDs f newFormulas)
    clausifyS f@(Implication [v, Conjunction cs]) = do
      let newFormulas = map (implication v) cs
      return (newFormulas, RightCs f newFormulas)
    clausifyS f@(Implication (x : y : z : is)) = do
      let newFormula = Implication (conjunction x y : z : is)
      return ([Implication (conjunction x y : z : is)], RightImpl f newFormula)
    clausifyS f@(Implication [x, Disjunction ds]) = do
      aliases <- MD.mapM (aliasS False) ds
      let (newDs, newAliases) = BF.second MB.catMaybes $ unzip aliases
      let newFormula = implication x (foldr1 disjunction newDs)
      return (newFormula : newAliases, Aliasing f newFormula newAliases)
    clausifyS i@(Implication (Conjunction cs : is)) = do
      let (_, rhs) = asPair i
      aliases <- MD.mapM (aliasS True) cs
      let (newCs, newAliases) = BF.second MB.catMaybes $ unzip aliases
      let newFormula = implication (foldr1 conjunction newCs) rhs
      return (newFormula : newAliases, Aliasing i newFormula newAliases)
    clausifyS i1@(Implication (i2@(Implication (x: is1)) : is2)) = do
      let (_, rhs1) = asPair i1
      let (_, rhs2) = asPair i2
      (aliasX, correspondanceX) <- aliasS False x
      (aliasY, correspondanceY) <- aliasS True rhs2
      (aliasZ, correspondanceZ) <- aliasS False rhs1

      let newAliases = MB.catMaybes [correspondanceX, correspondanceY, correspondanceZ]
      let newFormula = implication (implication aliasX aliasY) aliasZ 
      return (newFormula : newAliases, Aliasing i1 newFormula newAliases)

    clausifyS x = do
      let newFormula = implication top x
      return ([newFormula], MakeImpl x newFormula)

    aliasS :: Bool -> PlainFormula -> ST.State ClausificationState (PlainFormula, Maybe PlainFormula)
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

    freshS :: ST.State ClausificationState PlainFormula
    freshS = ST.state (\s -> (variable $ show $ fst s, BF.first (+ 1) s))

    putSequent :: (PlainSequent, ClausificationRule) -> ST.State ClausificationState ()
    putSequent seq = ST.state (\st -> ((), BF.second (seq:) st))

    clausifyLoopS :: PlainSequent -> ST.State (Int, [(PlainSequent, ClausificationRule)]) PlainSequent

    -- trace ("Flats: " ++ show f ++ " Impls: " ++ show i ++ " Rem: " ++ show (nph : npt)) $ do
    clausifyLoopS s@(UnclausifiedPlainSequent f i (nph : npt) g) = trace ("F: " ++ (unlines $ map formulaToString f) ++ " I: " ++ (unlines $ map formulaToString i) ++ " U: " ++ (unlines $ map show (nph:npt)) ) $ do
      case Clause.flatClauseFromFormula nph of
        Just clause -> do
          putSequent (s, AsFlat nph clause)
          clausifyLoopS (UnclausifiedPlainSequent (clause:f) i npt g)
        Nothing -> case Clause.implClauseFromFormula nph of
                      Just clause -> do
                        putSequent (s, AsImpl clause)
                        clausifyLoopS (UnclausifiedPlainSequent f (clause:i) npt g)
                      Nothing -> do
                        (clausified, rule) <- clausifyS nph
                        putSequent (s, rule)
                        clausifyLoopS (UnclausifiedPlainSequent f i (clausified ++ npt) g)

    clausifyLoopS s@(UnclausifiedPlainSequent f i [] g) = do
      putSequent (s, AsIntuit)
      return (IntuitPlainSequent f i g)
    clausifyLoopS _ = error ""


createAssertion :: (PlainFormula -> Z3.AST) -> Z3.Context -> PlainFormula -> IO Z3.AST
createAssertion vs ctx = createZ3Formula
  where
    createZ3Formula :: PlainFormula -> IO Z3.AST
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
    createZ3Formula v@(Atom _) = return $ vs v
