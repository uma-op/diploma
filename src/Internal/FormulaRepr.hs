module Internal.FormulaRepr where

import Internal.ParseProblem(Form(..))
import Formula (Formula(..), conjunction, implication, bottom, disjunction, variable)
import Internal.Clausify (Clause, (:->)(..), ImplClause)
import qualified Internal.Clausify as Clausify

import qualified Data.Foldable as Foldable
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Set as Set
import Data.Set (Set)

formulaToForm :: Formula -> Form
formulaToForm Bottom = FALSE
formulaToForm (Variable v) = Atom v
formulaToForm (Conjunction cs) = Foldable.foldr1 (:&:) (map formulaToForm cs)
formulaToForm (Disjunction ds) = Foldable.foldr1 (:|:) (map formulaToForm ds)
formulaToForm (Implication [x, y]) | x == y = TRUE
formulaToForm (Implication is) = Foldable.foldr1 (:=>:) (map formulaToForm is)

formToFormula :: Form -> Formula
formToFormula FALSE = Bottom
formToFormula TRUE = implication Bottom Bottom
formToFormula (Atom v) = Variable v
formToFormula (lhs :&: rhs) = conjunction (formToFormula lhs) (formToFormula rhs)
formToFormula (lhs :|: rhs) = disjunction (formToFormula lhs) (formToFormula rhs)
formToFormula (lhs :=>: rhs) = implication (formToFormula lhs) (formToFormula rhs)
formToFormula (lhs :<=>: rhs) = conjunction (implication lhsFormula rhsFormula) (implication rhsFormula lhsFormula)
  where
    lhsFormula = formToFormula lhs
    rhsFormula = formToFormula rhs

flatClauseToFormula :: Clause -> Formula
flatClauseToFormula ([] :-> ds) = Foldable.foldr1 disjunction (map variable ds)
flatClauseToFormula (cs :-> ds) =
  implication
    (Foldable.foldr1 conjunction (map variable cs))
    (Foldable.foldr1 disjunction (map variable ds))

implClauseToFormula :: ImplClause -> Formula
implClauseToFormula ((a :-> b) :-> c) = implication (implication (variable a) (variable b)) (variable c)

clausify :: Formula -> (Set Formula, Set Formula)
clausify formula =
  Bifunctor.bimap
  (Set.fromList . map flatClauseToFormula)
  (Set.fromList . map implClauseToFormula)
  (Clausify.clausify [formulaToForm formula])
