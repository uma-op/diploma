module Refactoring.Prover.Clausify(module Refactoring.Prover.Clausify) where

import Data.Maybe (fromJust, catMaybes)
import Data.Bifunctor (Bifunctor(second, first))
import Control.Monad.State

import Refactoring.Formula.Formula
import Refactoring.Formula.Atom
import Refactoring.Sequent.Unclausified
import Refactoring.Sequent.Intuit
import Refactoring.Sequent.Annotated
import Refactoring.Clause.Impl
import Refactoring.Clause

import Refactoring.Prover.CArrow
import Control.Applicative (asum)

import Fmt
import Refactoring.Clause.Flat (implImpliesFlat)
import Refactoring.Utils.Formatting (joinBy)

newtype ClausificationState_ = ClausificationState Int

aliasS :: Bool -> Formula_ -> State ClausificationState_ (Atom_, Maybe Formula_)
aliasS _ (Atom a) = return (a, Nothing)
aliasS isReversed f = do
  (ClausificationState i) <- get
  put (ClausificationState (i + 1))

  let freshAtom = Variable $ "v" ++ show i
  let freshVariable = Atom freshAtom
  if isReversed
    then return (freshAtom, Just $ implication f freshVariable)
    else return (freshAtom, Just $ implication freshVariable f)

data ClausificationRule_ a c =
  AsImpl (Unclausified_ a c) (ClausificationRule_ a c) |
  AsFlat (Unclausified_ a c) (ClausificationRule_ a c) |
  ImplImpliesFlat (Unclausified_ a c) (ClausificationRule_ a c) |

  MakeImpl (Unclausified_ a c) (ClausificationRule_ a c) |
  LeftDs (Unclausified_ a c) (ClausificationRule_ a c) |
  RightCs (Unclausified_ a c) (ClausificationRule_ a c) |
  Uncurry (Unclausified_ a c) (ClausificationRule_ a c) |
  Aliasing (Unclausified_ a c) (ClausificationRule_ a c) |

  FinishClausification (Unclausified_ a c) (Intuit_ a c) |  -- when just finished clausification
  StartCArrow (Unclausified_ a c) (CArrowRule_ a c)         -- when sequent has empty unclausified list

type UnclausifiedII = Unclausified_ () ()
type ClausificationRuleII = ClausificationRule_ () ()
type ClausificationRuleSignature = UnclausifiedII -> Maybe (State ClausificationState_ ClausificationRuleII)

clausificationRules :: [ClausificationRuleSignature]
clausificationRules = [ applyFinishClausification,
                        applyAsImpl,
                        applyAsFlat,
                        applyLeftDs,
                        applyRightCs,
                        applyUncurry,
                        applyAliasing,
                        applyMakeImpl
                      ]

clausify :: UnclausifiedII -> State ClausificationState_ ClausificationRuleII
clausify ucseq = do
  let appliedRules = map ($ ucseq) clausificationRules
  fromJust $ asum appliedRules

applyAsImpl :: ClausificationRuleSignature
applyAsImpl ucseq@(Unclausified flats impls (uc : ucs) goal) = do
  impl <- fromFormula $ annotated uc
  let sequent = Unclausified flats (Annotated () impl : impls) ucs goal
  
  return $ do
    rule <- clausify sequent
    return $ AsImpl ucseq rule

applyAsImpl _ = Nothing

applyAsFlat :: ClausificationRuleSignature
applyAsFlat ucseq@(Unclausified flats impls (uc : ucs) goal) = do
  flat <- fromFormula $ annotated uc
  let sequent = Unclausified (Annotated () flat : flats) impls ucs goal

  return $ do
      rule <- clausify sequent
      return $ AsFlat ucseq rule
applyAsFlat _ = Nothing

applyMakeImpl :: ClausificationRuleSignature
applyMakeImpl ucseq@(Unclausified flats impls (uc : ucs) goal) = do
  let iuc = Annotated () (implication top (annotated uc))
  let sequent = Unclausified flats impls (iuc : ucs) goal
  return $ do
    rule <- clausify sequent
    return $ MakeImpl ucseq rule
applyMakeImpl _ = Nothing

applyLeftDs :: ClausificationRuleSignature
applyLeftDs ucseq@(Unclausified flats impls (Annotated () (Implication (Disjunction ds : is)) : ucs) goal) = do
  let newIs = [Annotated () (Implication (d : is)) | d <- ds]
  let sequent = Unclausified flats impls (newIs ++ ucs) goal
  return $ do
    rule <- clausify sequent
    return $ LeftDs ucseq rule
applyLeftDs _ = Nothing

applyRightCs :: ClausificationRuleSignature
applyRightCs ucseq@(Unclausified flats impls (Annotated () (Implication [x, Conjunction cs]) : ucs) goal) = return $ do
  let newIs = [Annotated () (Implication [x, c]) | c <- cs]
  let sequent = Unclausified flats impls (newIs ++ ucs) goal
  rule <- clausify sequent
  return $ RightCs ucseq rule

applyRightCs _ = Nothing

applyUncurry :: ClausificationRuleSignature
applyUncurry ucseq@(Unclausified flats impls (Annotated () (Implication is@(_ : _ : _ : _)) : ucs) goal) = return $ do
  let sequent = Unclausified flats impls (Annotated () (Implication [Conjunction $ init is, last is]) : ucs) goal
  rule <- clausify sequent
  return $ Uncurry ucseq rule
applyUncurry _ = Nothing

applyAliasing :: ClausificationRuleSignature
applyAliasing ucseq@(
  Unclausified flats impls
    (Annotated () is@(Implication (Implication (_ : _ : _) : _ : _)) : ucs) goal) = return $ do

  let (lhs, c) = second fromJust $ split is
  let (a, b) = second fromJust $ split lhs

  (freshA, aliasA) <- aliasS False a
  (freshB, aliasB) <- aliasS True b
  (freshC, aliasC) <- aliasS False c

  let sequent =
        Unclausified
          flats
          (Annotated ()
            (Impl
              (Annotated () freshA)
              (Annotated () freshB)
              (Annotated () freshC)) : impls)
          ((Annotated () <$> catMaybes [aliasA, aliasB, aliasC]) ++ ucs) goal

  rule <- clausify sequent
  return $ Aliasing ucseq rule

applyAliasing ucseq@(Unclausified flats impls (Annotated () is@(Implication (Conjunction cs : _ : _)) : ucs) goal) = return $ do
  let (Conjunction as, b) = second fromJust $ split is
  aliased <- mapM (aliasS True) as
  let (vars, aliases) = unzip $ first Atom <$> aliased
  let sequent =
        Unclausified
          flats
          impls
          ((Annotated () <$> (implication (Conjunction vars) b : catMaybes aliases)) ++ ucs) goal
  rule <- clausify sequent
  return $ Aliasing ucseq rule

applyAliasing ucseq@(Unclausified flats impls (Annotated () is@(Implication [a, Disjunction bs]) : ucs) goal) = return $ do
  aliased <- mapM (aliasS False) bs
  let (vars, aliases) = unzip $ first Atom <$> aliased
  let sequent =
        Unclausified
          flats
          impls
          ((Annotated () <$> (implication a (Disjunction vars) : catMaybes aliases)) ++ ucs)
          goal

  rule <- clausify sequent
  return $ Aliasing ucseq rule

applyAliasing _ = Nothing

applyFinishClausification :: ClausificationRuleSignature
applyFinishClausification ucseq@(Unclausified flats impls [] goal) = return $ do
    return $ applyImplImpliesFlat (annotated <$> impls) ucseq
    where
      applyImplImpliesFlat :: [Impl_ ()] -> UnclausifiedII -> ClausificationRuleII
      applyImplImpliesFlat (i:is) ucseq@(Unclausified flats impls ucs goal) =
        ImplImpliesFlat
          ucseq
          (applyImplImpliesFlat is (Unclausified (Annotated () (implImpliesFlat i) : flats ) impls ucs goal))
      applyImplImpliesFlat [] ucseq@(Unclausified flats impls ucs goal) = FinishClausification ucseq (Intuit flats impls goal)

applyFinishClausification _ = Nothing
