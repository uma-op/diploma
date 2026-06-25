module Refactoring.Prover.Annotate(module Refactoring.Prover.Annotate) where

import Control.Monad
import Control.Monad.State
import Data.Map (Map)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.List as List

import Refactoring.Sequent.Classic
import Refactoring.Prover.Clausify
import Refactoring.Lambda.Lambda
import Refactoring.Prover.CArrow
import Refactoring.Prover.LJT
import Refactoring.Formula.Formula
import qualified Refactoring.Formula.Atom as Atom
import Refactoring.Formula
import Refactoring.Sequent.Annotated
import Refactoring.Clause.Flat
import Refactoring.Clause.Impl
import Refactoring.Sequent.Intuit
import Refactoring.Sequent.Unclausified

annotateClausification :: ClausificationRule_ () () -> State Environment (ClausificationRule_ Lambda_ ())
annotateClausification (AsImpl useq rule implFormula implClause _) = do
  annotatedRule <- annotateClausification rule
  let (Unclausified flats impls uncs goal) = rootClausification annotatedRule 
  let (Just annotatedClause, impls') = extract ((== implClause) . annotated) impls

  return $
    AsImpl
      (Unclausified flats impls' (Annotated (annotation annotatedClause) implFormula : uncs) goal)
      annotatedRule implFormula implClause []

annotateClausification (AsFlat useq rule f f' _) = do
  annotatedRule <- annotateClausification rule
  let (Unclausified flats impls uncs goal) = rootClausification annotatedRule
  let goalTerm = fst $ annotation goal 
  f'Term <- getTerm f'
  fTerm <- getTerm f
  substitution <- case f of
        Atom a -> return $ Substitution (varName f'Term) (Const (Sum 1 1 fTerm))
        Disjunction ds -> return $ Substitution (varName f'Term) (Const fTerm)
        Implication [Atom a, Atom b] -> do
          captureTerm <- getNewTerm
          return $ Substitution (varName f'Term) (Abstraction [varName captureTerm] $ Sum 1 1 (Application [fTerm, Proj 1 1 captureTerm]))
        Implication [Atom a, Disjunction ds] -> do
          captureTerm <- getNewTerm
          return $ Substitution (varName f'Term) (Abstraction [varName captureTerm] $ Application [fTerm, Proj 1 1 captureTerm])
        Implication [Conjunction cs, Atom a] -> do
          captureTerm <- getNewTerm
          return $ Substitution (varName f'Term) (Abstraction [varName captureTerm] $ Sum 1 1 $ Application [fTerm, captureTerm])
        Implication [Conjunction cs, Disjunction ds] -> return $ Substitution (varName f'Term) fTerm
        _ -> undefined

  let substituted = substitute goalTerm substitution

  let flats' = snd $ extract ((== f') . annotated) flats
  let uncs' = Annotated fTerm f : uncs

  return $ 
    AsFlat
      (Unclausified flats' impls uncs' (Annotated (substituted, ()) (annotated goal)))
      annotatedRule f f' [substitution]

annotateClausification (ImplImpliesFlat useq rule implClause flatClause _) = do
  annotatedRule <- annotateClausification rule
  let (Unclausified flats impls uncs goal) = rootClausification annotatedRule
  let (_, flats') = extract ((== flatClause) . annotated) flats
  implTerm <- getTerm implClause
  flatTerm <- getTerm flatClause
  captureTerm <- getNewTerm
  let substitution =
        Substitution
          (varName flatTerm)
          (Abstraction [varName captureTerm] $ Sum 1 1 $ Application [implTerm, Const (Proj 1 1 captureTerm)])

  return $
    ImplImpliesFlat
      (Unclausified flats' impls uncs (Annotated ((substitute (fst $ annotation goal) substitution),()) (annotated goal)))
      annotatedRule implClause flatClause [substitution]

annotateClausification (MakeImpl useq rule f f' _) = do
  annotatedRule <- annotateClausification rule
  let (Unclausified flats impls uncs goal) = rootClausification annotatedRule
  f'Term <- getTerm f'
  fTerm <- getTerm f
  captureTerm <- getNewTerm
  let substitution = Substitution (varName f'Term) (Abstraction [varName captureTerm] fTerm)
  let uncs' = Annotated fTerm f : snd (extract ((== f') . annotated) uncs)

  return $
    MakeImpl
      (Unclausified flats impls uncs' (Annotated ((substitute (fst $ annotation goal) substitution), ()) (annotated goal)))
      annotatedRule f f' [substitution]

annotateClausification (LeftDs useq rule f fs _) = do
  annotatedRule <- annotateClausification rule
  let (Unclausified flats impls uncs goal) = rootClausification annotatedRule
  fTerm <- getTerm f
  fsTerms <- mapM getTerm fs
  let n = length fsTerms
  captureTerms <- replicateM n getNewTerm

  let substitutions = [
          Substitution (varName fsTerm) (Abstraction [varName captureTerm] $ Application [fTerm, Sum n i captureTerm]) 
          | (i, captureTerm, fsTerm) <- zip3 [1..] captureTerms fsTerms
        ]
  
  let substituted = foldl substitute (fst $ annotation goal) substitutions
  let uncs' = Annotated fTerm f : foldl (\c e -> snd $ extract ((== e) . annotated) c) uncs fs

  return $
    LeftDs
      (Unclausified flats impls uncs' (Annotated (substituted, ()) (annotated goal)))
      annotatedRule f fs substitutions

annotateClausification (RightCs useq rule f fs _) = do
  annotatedRule <- annotateClausification rule
  let (Unclausified flats impls uncs goal) = rootClausification annotatedRule
  fTerm <- getTerm f
  fsTerms <- mapM getTerm fs
  let n = length fsTerms
  captureTerms <- replicateM n getNewTerm

  let substitutions = [
          Substitution (varName fsTerm) (Abstraction [varName captureTerm] $ Proj n i $ Application [fTerm, captureTerm]) 
          | (i, captureTerm, fsTerm) <- zip3 [1..] captureTerms fsTerms
        ]
  
  let substituted = foldl substitute (fst $ annotation goal) substitutions
  let uncs' = Annotated fTerm f : foldl (\c e -> snd $ extract ((== e) . annotated) c) uncs fs

  return $
    RightCs
      (Unclausified flats impls uncs' (Annotated (substituted, ()) (annotated goal)))
      annotatedRule f fs substitutions

{- 
 - f': (a1 /\ ... /\ an) -> b |- g
 - f: a1 -> ... -> an -> b |- g
 -
 - f' := \p.fP(n, 1, p)P(n, 2, p)...P(n, n, p)
 - -}

annotateClausification (Uncurry useq rule f@(Implication is) f' _) = do
  annotatedRule <- annotateClausification rule
  let (Unclausified flats impls uncs goal) = rootClausification annotatedRule
  fTerm <- getTerm f
  f'Term <- getTerm f'
  captureTerm <- getNewTerm
  let n = length is - 1
  let substitution =
        Substitution
          (varName f'Term)
          (Abstraction [varName captureTerm] $ Application ([fTerm] ++ [Proj n i captureTerm | i <- [1..n]]))
  let uncs' = Annotated fTerm f : snd (extract ((== f') . annotated) uncs)
  return $
    Uncurry 
      (Unclausified flats impls uncs' (Annotated ((substitute (fst $ annotation goal) substitution), ()) (annotated goal)))
      annotatedRule f f' [substitution]

annotateClausification (Aliasing useq rule f f' hs _) = do
  annotatedRule <- annotateClausification rule
  let (Unclausified flats impls uncs goal) = rootClausification annotatedRule
  fTerm <- getTerm f
  let uncs' = Annotated fTerm f : foldl (\c e -> snd $ extract ((== e) . annotated) c) uncs (f' : hs)
  f'Term <- getTerm f'
  hTerms <- mapM getTerm hs
  let hSubstitutions = [
        Substitution (varName hTerm) (Product [])
        | hTerm <- hTerms]
  let hSubstituted = foldl substitute (fst $ annotation goal) hSubstitutions
  let fSubstitution = Substitution (varName f'Term) fTerm
  let fSubstituted = substitute hSubstituted fSubstitution

  return $
    Aliasing 
      (Unclausified flats impls uncs' (Annotated (fSubstituted, ()) (annotated goal)))
      annotatedRule f f' hs (fSubstitution : hSubstitutions)

annotateClausification (StartCArrow useq carrowRule) = do
  annotatedCArrow <- annotateCArrow carrowRule
  let (Intuit flats impls goal) = rootCArrow annotatedCArrow

  return $
    StartCArrow
      (Unclausified flats impls [] goal)
      annotatedCArrow

annotateClausification _ = undefined

annotateCArrow :: CArrowRule_ () () -> State Environment (CArrowRule_ Lambda_ ())
annotateCArrow (ExCPL0 (Intuit _ impls _) ljtRule _) = do
  annotatedLJT <- annotateLJT ljtRule
  let (Classic flats _ goal) = rootLJT annotatedLJT
  implAnnotations <- mapM getTerm (annotated <$> impls)
  let annotatedImpls = [
        Annotated ann (annotated impl)
        | (impl, ann) <- zip impls implAnnotations]

  return $
    ExCPL0
      (Intuit flats annotatedImpls goal)
      annotatedLJT []

{- 
 - R0 |- \p.(\p1...pn.\p0.q)P(n, 1, p)P(n, 2, p)...P(n, n, p) : (a1 /\ ... /\ an) -> a -> b
 - ----------------------------------------------------------------
 - R0 |- \p1...pn.\p0.q : a1 -> ... -> an -> a -> b
 - ----------------------------------------------
 - R0, p0: a, p1: a1, ..., pn: an |- q: b    R0, phi: (a1 /\ ... /\ an) -> c, X |- g
 - ---------------------------------------------------------------------------------  l: (a -> b) -> c
 -                                      R0, X |- g [phi := ]
 -
 - h = \p.(\p1...pn.\p0.q)P(n, 1, p)P(n, 2, p)...P(n, n, p)
 - phi := \x.l(hx)
 -
 - -}
  
annotateCArrow (ExCPL1 iseq ljtRule rule newClause@(Flat cs _) learnedImpl@(Impl a _ _) _) = do
  annotatedLJT <- annotateLJT ljtRule
  let (Classic flats _ b) = rootLJT annotatedLJT

  annotatedCArrow <- annotateCArrow rule
  let (Intuit _ impls goal) = rootCArrow annotatedCArrow

  phi <- getTerm newClause
  lambda <- getTerm learnedImpl

  asTerms <- mapM getTerm (annotated <$> cs)
  aTerm <- getTerm (annotated a)
  captureTerm <- getNewTerm
  let n = length cs
  let projections = [Proj n i captureTerm | i <- [1..n]]

  let classicTerm =
        Abstraction [varName captureTerm] $
          Application (Abstraction (varName <$> asTerms ++ [aTerm]) (fst $ annotation b) : projections)

  x <- getNewTerm
  let substitution =
        Substitution
          (varName phi) $ reduce
          (Abstraction [varName x] $ Sum 1 1 $ Application [lambda, Application [classicTerm, x]])

  return $
    ExCPL1 
      (Intuit flats impls (Annotated ((substitute (fst $ annotation goal) substitution), ()) (annotated goal)))
      annotatedLJT
      annotatedCArrow
      newClause
      learnedImpl
      [substitution]

annotateCArrow _ = undefined

annotateLJT :: LJTRule_ () () -> State Environment (LJTRule_ Lambda_ ())
annotateLJT (Axiom (Classic flats assumptions goal)) = do
  annotatedFlats <- sequence [
    do t <- getTerm flat
       return (Annotated t flat)
    | (Annotated _ flat) <- flats]

  annotatedAssumptions <- sequence [
    do t <- getTerm assumption
       return (Annotated (t, ()) assumption)
    | (Annotated _ assumption) <- assumptions]

  annotatedGoal <- do t <- getTerm (annotated goal)
                      return (Annotated (t, ()) (annotated goal))

  return $ Axiom (Classic annotatedFlats annotatedAssumptions annotatedGoal)

{- 
 - f': (a_1 /\ ... /\ a_i-1 /\ a_i+1 /\ ... /\ a_n) -> B, a: a_i ... |- g
 - ---------------------------------------------------------------
 - f: (a_1 /\ ... /\ a_i /\ ... /\ a_n) -> B, a_i ... |- g
 -
 - f' := \p.f(Ins(n-1, i, p, a))
 -
-}

  
annotateLJT (ReduceConjunction cseq rule clause@(Flat cs ds) atom _) = do
  let n = List.length cs
  let (Just atomIndex) = List.findIndex ((== atom) . annotated) cs
  let i = atomIndex + 1
  let reduced = Flat (List.take atomIndex cs ++ List.drop i cs) ds

  annotatedRule <- annotateLJT rule
  let (Classic flats' assumptions' goal') = rootLJT annotatedRule

  let (Just f', flats) = extract ((== reduced) . annotated) flats'
  let a = case atom of
            Atom.Top -> Annotated (Product [], ()) Atom.Top 
            _ -> fromJust $ List.find ((== atom) . annotated) assumptions'
  f <- getTerm clause
  p <- getNewTerm

  let substitution =
        Substitution
          (varName $ annotation f') 
          (Abstraction [varName p] (Application [f, Insert (n - 1) i p (fst $ annotation a)]))

  return $ ReduceConjunction
    (Classic
      (Annotated f clause : flats)
      assumptions'
      (Annotated ((substitute (fst $ annotation goal') substitution), ()) (annotated goal'))
    )
    annotatedRule clause atom
    [substitution]

{- 
 - f_1: a_1, ... |- g_1: g  f_2: a_2, ... |- g_2: g ... f_n: a_n, ... |- g_n: g
 - -----------------------------------------------------------------------------------------------------
 - f: () -> (a_1 \/ a_2 \/ ... \/ a_n), ... |- g: case(f<>, [(f_1, g_1), (f_2, g_2), ..., (f_n, g_n)])
 -
-}

annotateLJT (SplitDisjunction cseq rules clause@(Flat _ ds) _) = do
  annotatedBranches <- mapM annotateLJT rules
  let roots = rootLJT <$> annotatedBranches
  let cases = [
          let (Just a, _) = extract ((== atom) . annotated) assumptions
          in (varName $ fst $ annotation a, fst $ annotation goal)
          | ((Annotated () atom), (Classic flats assumptions goal)) <- zip ds roots
        ]
  f <- getTerm clause
  let (Classic flats assumptions goal) = head roots
  let newFlats = (Annotated f clause) : flats
  let newAssumptions = snd $ extract ((== annotated (head ds)) . annotated) assumptions

  return $
    SplitDisjunction
      (Classic
        newFlats
        newAssumptions
        (Annotated ((Case (Application [f, Product []]) cases), ()) (annotated goal))
      )
      annotatedBranches
      clause []

extract :: (a -> Bool) -> [a] -> (Maybe a, [a])
extract pred list =
  case List.break pred list of
    (list1, []) -> (Nothing, list1)
    (list1, found : list2) -> (Just found, list1 ++ list2)
  
