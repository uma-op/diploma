{-# LANGUAGE GADTs #-}

module Clausify where

import qualified Control.Monad as MD
import qualified Control.Monad.State as ST
import qualified Data.Bifunctor as BF
import qualified Data.Maybe as MB
import Formula
  (
    PlainFormula (..),
    asPair,
    conjunction,
    disjunction,
    implication,
    isAtom,
    top,
    variable,
    Atom, plain
  )

import Clause (FlatClauseFormula, ImplClauseFormula)
import qualified Clause
import qualified Z3.Base as Z3
import qualified Data.List as List
import Proof

type ClausificationState = (Int, [(PlainSequent, ClausificationRule)])

clausify :: PlainFormula -> (PlainSequent, [(PlainSequent, ClausificationRule)])
clausify formula =
  (result, history)
  where
    (initial, toGoalify) = -- traceWith (("Goalified: " ++) . show) $
      case formula of 
        Implication impls -> (init impls, last impls)
        _ -> ([], formula)


    b = implication toGoalify $ plain q
    q = atom $ variable "$"

    (result, (_, history)) = ST.runState (clausifyLoopS (UnclausifiedSequent [] [] (b:initial) q)) (0, [])

    clausifyS :: PlainFormula -> ST.State ClausificationState ([PlainFormula], ClausificationRule)
    clausifyS (Implication [Disjunction ds, v@(Atom _)]) = return (map (`implication` v) ds, LeftDs)
    clausifyS (Implication [v@(Atom _), Conjunction cs]) = return (map (implication v) cs, RightCs)
    clausifyS (Implication (x : y : z : is)) = return ([Implication (conjunction x y : z : is)], RightImpl)
    clausifyS (Implication [x, Disjunction ds]) = do
      aliases <- MD.mapM (aliasS False) ds
      let (newDs, additional) = BF.second MB.catMaybes $ unzip aliases
      return (implication x (foldr1 disjunction newDs) : additional, RightDs)
    clausifyS i@(Implication (Conjunction cs : is)) = do
      let (_, rhs) = asPair i
      aliases <- MD.mapM (aliasS True) cs
      let (newCs, additional) = BF.second MB.catMaybes $ unzip aliases
      return (implication (foldr1 conjunction newCs) rhs : additional, LeftCs)
    clausifyS i1@(Implication (i2@(Implication (x: is1)) : is2)) = do
      let (_, rhs1) = asPair i1
      let (_, rhs2) = asPair i2
      (aliasX, correspondanceX) <- aliasS False x
      (aliasY, correspondanceY) <- aliasS True rhs2
      (aliasZ, correspondanceZ) <- aliasS False rhs1
      return (implication (implication aliasX aliasY) aliasZ : MB.catMaybes [correspondanceX, correspondanceY, correspondanceZ], LeftImpl)
    clausifyS x = return ([implication top x], MakeImpl)

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

    putSequent :: (PlainSequent, ClausificationRule) -> ST.State (Int, [(PlainSequent, ClausificationRule)]) ()
    putSequent seq = ST.state (\st -> ((), BF.second (seq:) st))

    clausifyLoopS :: PlainSequent -> ST.State (Int, [(PlainSequent, ClausificationRule)]) PlainSequent

    -- trace ("Flats: " ++ show f ++ " Impls: " ++ show i ++ " Rem: " ++ show (nph : npt)) $ do
    clausifyLoopS s@(UnclausifiedSequent f i (nph : npt) g) = do
      case Clause.flatClauseFromFormula nph of
        Just clause -> do
          putSequent (s, AsFlat)
          clausifyLoopS (UnclausifiedSequent (clause:f) i npt g)
        Nothing -> case Clause.implClauseFromFormula nph of
                      Just clause -> do
                        putSequent (s, AsImpl)
                        clausifyLoopS (UnclausifiedSequent f (clause:i) npt g)
                      Nothing -> do
                        (clausified, rule) <- clausifyS nph
                        putSequent (s, rule)
                        clausifyLoopS (UnclausifiedSequent f i (clausified ++ npt) g)

    clausifyLoopS s@(UnclausifiedSequent f i [] g) = do
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
