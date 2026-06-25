module Refactoring.Prover.Clausify(module Refactoring.Prover.Clausify) where

import Data.Maybe (fromJust, catMaybes)
import Data.Bifunctor (Bifunctor(second, first))
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map

import Refactoring.Formula.Formula
import Refactoring.Formula.Atom
import Refactoring.Sequent.Unclausified
import Refactoring.Sequent.Intuit
import Refactoring.Sequent.Annotated
import Refactoring.Clause.Impl
import Refactoring.Clause.Flat
import Refactoring.Formula

import Refactoring.Prover.CArrow
import Control.Applicative (asum)

import Fmt
import Refactoring.Clause.Flat (implImpliesFlat)
import Refactoring.Utils.Formatting (joinBy)
import qualified Data.Bifunctor as Bifunctor
import Refactoring.Lambda.Lambda (Substitution_)

data ClausificationState_ =
  ClausificationState
    Int  -- last named atom
    (Map Formula_ Atom_)  -- aliases for implies
    (Map Formula_ Atom_)  -- aliases for implied by

aliasS :: Bool -> Formula_ -> State ClausificationState_ (Atom_, Maybe Formula_)
aliasS _ (Atom a) = return (a, Nothing)
aliasS isReversed f = do
  (ClausificationState i c1 c2) <- get
  let lookupMap = if isReversed then c1 else c2
  let implWithReverse = if isReversed then implication else flip implication
  case Map.lookup f lookupMap of
    Just a -> return (a, Just $ implWithReverse f (Atom a))
    Nothing -> do
      let freshAtom = Variable $ "v" ++ show i
      let freshVariable = Atom freshAtom
      if isReversed
        then put (ClausificationState (i + 1) (Map.insert f freshAtom c1) c2)
        else put (ClausificationState (i + 1) c1 (Map.insert f freshAtom c2))
      return (freshAtom, Just $ implWithReverse f freshVariable)

data ClausificationRule_ a c =
  AsImpl
    (Unclausified_ a c)  -- root
    (ClausificationRule_ a c)  -- branch
    Formula_   -- moved formula
    (Impl_ c)  -- result clause
    [Substitution_]
  |
  AsFlat
    (Unclausified_ a c)  -- root
    (ClausificationRule_ a c)  -- branch
    Formula_  -- moved formula
    (Flat_ c)  -- result clause
    [Substitution_]
  |
  ImplImpliesFlat
    (Unclausified_ a c)  -- root
    (ClausificationRule_ a c)  -- branch
    (Impl_ c)  -- impl that implies
    (Flat_ c)  -- flat implied by
    [Substitution_]
  |

  MakeImpl
    (Unclausified_ a c)  -- root
    (ClausificationRule_ a c)  -- branch
    Formula_  -- non implication formula
    Formula_  -- implication formula
    [Substitution_]
  |
  LeftDs
    (Unclausified_ a c)  -- root
    (ClausificationRule_ a c)  -- branch
    Formula_  -- implication
    [Formula_]  -- result formulas
    [Substitution_]
  |
  RightCs
    (Unclausified_ a c)  -- root
    (ClausificationRule_ a c)  -- branch
    Formula_   -- implication
    [Formula_]  -- result formulas
    [Substitution_]
  |
  Uncurry
    (Unclausified_ a c)  -- root
    (ClausificationRule_ a c)  -- branch
    Formula_  -- curried
    Formula_  -- uncurried
    [Substitution_]
  |
  Aliasing
    (Unclausified_ a c)  -- root
    (ClausificationRule_ a c)  -- branch
    Formula_  -- complex formula
    Formula_  -- aliased
    [Formula_]  -- aliases
    [Substitution_]
  |

  FinishClausification (Unclausified_ a c) (Intuit_ a c) |  -- when just finished clausification
  StartCArrow (Unclausified_ a c) (CArrowRule_ a c)         -- when sequent has empty unclausified list

instance Functor (ClausificationRule_ a) where
  fmap f (AsImpl useq rule x y subs) = AsImpl (fmap f useq) (fmap f rule) x (fmap f y) subs
  fmap f (AsFlat useq rule x y subs) = AsFlat (fmap f useq) (fmap f rule) x (fmap f y) subs
  fmap f (ImplImpliesFlat useq rule x y subs) = ImplImpliesFlat (fmap f useq) (fmap f rule) (fmap f x) (fmap f y) subs
  fmap f (MakeImpl useq rule x y subs) = MakeImpl (fmap f useq) (fmap f rule) x y subs
  fmap f (LeftDs useq rule x y subs) = LeftDs (fmap f useq) (fmap f rule) x y subs
  fmap f (RightCs useq rule x y subs) = RightCs (fmap f useq) (fmap f rule) x y subs
  fmap f (Uncurry useq rule x y subs) = Uncurry (fmap f useq) (fmap f rule) x y subs
  fmap f (Aliasing useq rule x y z subs) = Aliasing (fmap f useq) (fmap f rule) x y z subs
  fmap f (FinishClausification useq rule) = FinishClausification (fmap f useq) (fmap f rule)
  fmap f (StartCArrow useq rule) = StartCArrow (fmap f useq) (fmap f rule)

instance Bifunctor ClausificationRule_ where
  first f (AsImpl useq rule x y subs) = AsImpl (first f useq) (first f rule) x y subs
  first f (AsFlat useq rule x y subs) = AsFlat (first f useq) (first f rule) x y subs
  first f (ImplImpliesFlat useq rule x y subs) = ImplImpliesFlat (first f useq) (first f rule) x y subs
  first f (MakeImpl useq rule x y subs) = MakeImpl (first f useq) (first f rule) x y subs
  first f (LeftDs useq rule x y subs) = LeftDs (first f useq) (first f rule) x y subs
  first f (RightCs useq rule x y subs) = RightCs (first f useq) (first f rule) x y subs
  first f (Uncurry useq rule x y subs) = Uncurry (first f useq) (first f rule) x y subs
  first f (Aliasing useq rule x y z subs) = Aliasing (first f useq) (first f rule) x y z subs
  first f (FinishClausification useq rule) = FinishClausification (first f useq) (first f rule)
  first f (StartCArrow useq rule) = StartCArrow (first f useq) (first f rule)

  second = fmap

rootClausification :: ClausificationRule_ a c -> Unclausified_ a c
rootClausification (AsImpl useq _ _ _ _) = useq
rootClausification (AsFlat useq _ _ _ _) = useq
rootClausification (ImplImpliesFlat useq _ _ _ _) = useq
rootClausification (MakeImpl useq _ _ _ _) = useq
rootClausification (LeftDs useq _ _ _ _) = useq
rootClausification (RightCs useq _ _ _ _) = useq
rootClausification (Uncurry useq _ _ _ _) = useq
rootClausification (Aliasing useq _ _ _ _ _) = useq
rootClausification (FinishClausification useq _) = useq
rootClausification (StartCArrow useq _) = useq

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
    return $ AsImpl ucseq rule (annotated uc) impl []

applyAsImpl _ = Nothing

applyAsFlat :: ClausificationRuleSignature
applyAsFlat ucseq@(Unclausified flats impls (uc : ucs) goal) = do
  flat <- fromFormula $ annotated uc
  let sequent = Unclausified (Annotated () flat : flats) impls ucs goal

  return $ do
      rule <- clausify sequent
      return $ AsFlat ucseq rule (annotated uc) flat []
applyAsFlat _ = Nothing

applyMakeImpl :: ClausificationRuleSignature
applyMakeImpl ucseq@(Unclausified flats impls (uc : ucs) goal) = do
  let iuc = Annotated () (implication top (annotated uc))
  let sequent = Unclausified flats impls (iuc : ucs) goal
  return $ do
    rule <- clausify sequent
    return $ MakeImpl ucseq rule (annotated uc) (annotated iuc) []
applyMakeImpl _ = Nothing

applyLeftDs :: ClausificationRuleSignature
applyLeftDs ucseq@(Unclausified flats impls (Annotated () uc@(Implication (Disjunction ds : is)) : ucs) goal) = do
  let newIs = [Annotated () (Implication (d : is)) | d <- ds]
  let sequent = Unclausified flats impls (newIs ++ ucs) goal
  return $ do
    rule <- clausify sequent
    return $ LeftDs ucseq rule uc (annotated <$> newIs) []
applyLeftDs _ = Nothing

applyRightCs :: ClausificationRuleSignature
applyRightCs ucseq@(Unclausified flats impls (Annotated () uc@(Implication [x, Conjunction cs]) : ucs) goal) = return $ do
  let newIs = [Annotated () (Implication [x, c]) | c <- cs]
  let sequent = Unclausified flats impls (newIs ++ ucs) goal
  rule <- clausify sequent
  return $ RightCs ucseq rule uc (annotated <$> newIs) []

applyRightCs _ = Nothing

applyUncurry :: ClausificationRuleSignature
applyUncurry ucseq@(Unclausified flats impls (Annotated () uc@(Implication is@(_ : _ : _ : _)) : ucs) goal) = return $ do
  let uncurried = Implication [Conjunction $ init is, last is]
  let sequent = Unclausified flats impls (Annotated () uncurried : ucs) goal
  rule <- clausify sequent
  return $ Uncurry ucseq rule uc uncurried []
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

  let aliased = Implication [Implication [Atom freshA, Atom freshB], Atom freshC]
  let aliases = catMaybes [aliasA, aliasB, aliasC]

  let sequent =
        Unclausified
          flats
          impls
          ((Annotated () <$> (aliased : aliases)) ++ ucs) goal

  rule <- clausify sequent
  return $ Aliasing ucseq rule is aliased aliases []

applyAliasing ucseq@(Unclausified flats impls (Annotated () is@(Implication (Conjunction cs : _ : _)) : ucs) goal) = return $ do
  let (Conjunction as, b) = second fromJust $ split is
  aliasedAtoms <- mapM (aliasS True) as
  let (vars, aliases) = Bifunctor.bimap (fmap Atom) catMaybes $ unzip aliasedAtoms
  let aliased = implication (Conjunction vars) b
  let sequent =
        Unclausified
          flats impls
          ((Annotated () <$> (aliased : aliases)) ++ ucs) goal
  rule <- clausify sequent
  return $ Aliasing ucseq rule is aliased aliases []

applyAliasing ucseq@(Unclausified flats impls (Annotated () is@(Implication [a, Disjunction bs]) : ucs) goal) = return $ do
  aliasedAtoms <- mapM (aliasS False) bs
  let (vars, aliases) = Bifunctor.bimap (fmap Atom) catMaybes $ unzip aliasedAtoms
  let aliased = implication a (Disjunction vars)
  let sequent =
        Unclausified
          flats impls
          ((Annotated () <$> (aliased : aliases)) ++ ucs)
          goal

  rule <- clausify sequent
  return $ Aliasing ucseq rule is aliased aliases []

applyAliasing _ = Nothing

applyFinishClausification :: ClausificationRuleSignature
applyFinishClausification ucseq@(Unclausified flats impls [] goal) = return $ do
    return $ applyImplImpliesFlat (annotated <$> impls) ucseq
    where
      applyImplImpliesFlat :: [Impl_ ()] -> UnclausifiedII -> ClausificationRuleII
      applyImplImpliesFlat (i:is) ucseq@(Unclausified flats impls ucs goal) =
        ImplImpliesFlat
            ucseq
            (applyImplImpliesFlat is (Unclausified (Annotated () impliedFlat : flats) impls ucs goal))
            i impliedFlat []
        where
          impliedFlat = implImpliesFlat i
      applyImplImpliesFlat [] ucseq@(Unclausified flats impls ucs goal) =
        FinishClausification ucseq (Intuit flats impls goal)

applyFinishClausification _ = Nothing
