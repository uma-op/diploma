module Refactoring.Prover.LJT(module Refactoring.Prover.LJT) where 

import Refactoring.Sequent.Classic
import Refactoring.Clause.Flat
import Data.Bifunctor
import qualified Data.List as List
import Control.Applicative
import Data.Maybe

import Refactoring.Sequent.Annotated
import Refactoring.Formula.Atom
import Refactoring.Lambda.Lambda (Substitution_)

import Debug.Trace

data LJTRule_ a c =
  Axiom
    (Classic_ a c) -- root
  |
  SplitDisjunction
    (Classic_ a c) -- root
    [LJTRule_ a c] -- branches
    (Flat_ ())      -- clause that splitted
    [Substitution_]
  |
  ReduceConjunction
    (Classic_ a c) -- root
    (LJTRule_ a c) -- branch
    (Flat_ ())      -- clause to reduce
    Atom_          -- deleted atom
    [Substitution_]

rootLJT :: LJTRule_ a c -> Classic_ a c
rootLJT (Axiom cseq) = cseq
rootLJT (SplitDisjunction cseq _ _ _) = cseq
rootLJT (ReduceConjunction cseq _ _ _ _) = cseq

instance Functor (LJTRule_ a) where
  fmap f (Axiom cseq) = Axiom (fmap f cseq)
  fmap f (SplitDisjunction cseq rs splitted subs) = SplitDisjunction (fmap f cseq) (fmap f <$> rs) splitted subs
  fmap f (ReduceConjunction cseq r clause atom subs) = ReduceConjunction (fmap f cseq) (fmap f r) clause atom subs

instance Bifunctor LJTRule_ where
  first f (Axiom cseq) = Axiom (first f cseq)
  first f (SplitDisjunction cseq rs splitted subs) = SplitDisjunction (first f cseq) (first f <$> rs) splitted subs
  first f (ReduceConjunction cseq r clause atom subs) = ReduceConjunction (first f cseq) (first f r) clause atom subs

  second = fmap

ljt :: Classic_ () () -> LJTRule_ () ()
ljt cseq@(Classic flats assumptions goal) =
  fromJust $ asum (map ($ cseq) [applyAxiom, applyCs, applyDs])
  where
    applyAxiom :: Classic_ () () -> Maybe (LJTRule_ () ())
    applyAxiom cseq@(Classic flats assumptions goal) =
      if goal `elem` assumptions
        then Just (Axiom cseq)
        else Nothing

    applyCs :: Classic_ () () -> Maybe (LJTRule_ () ())
    applyCs cseq@(Classic flats assumptions goal) = do
      (atom, flat@(Annotated () (Flat cs ds))) <- maybeFoundCs
      let newClause = Flat (List.delete (reannotate (const ()) atom) cs) ds
      let newSequent = (Classic (Annotated () newClause : List.delete flat flats) assumptions goal)
      return
        (ReduceConjunction
          cseq
          (ljt newSequent)
          (annotated flat)
          (annotated atom) [])
      where
        maybeFoundCs = List.find (uncurry csPred) [(a', r') | a' <- (Annotated ((), ()) Top : assumptions), r' <- flats]
        csPred atom (Annotated () (Flat cs _)) = annotated atom `elem` map annotated cs

    applyDs :: Classic_ () () -> Maybe (LJTRule_ () ())
    applyDs cseq@(Classic flats assumptions goal) = do
      found@(Annotated () (Flat _ ds)) <- maybeFoundDs
      return $
        SplitDisjunction
          cseq
          (ljt <$> [
            Classic (List.delete found flats) (addAnnotation () d : assumptions) goal
            | d <- ds
          ])
          (annotated found) []
      where
        maybeFoundDs = List.find dsPred flats
        dsPred (Annotated () (Flat [] _)) = True
        dsPred _ = False

