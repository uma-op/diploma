module FormulaRepr where

import ParseProblem(Form(..))
import Formula (Formula(..), conjunction, implication, bottom, disjunction, variable)
import Clausify (Clause, (:->)(..), ImplClause)

formToFormula :: Form -> Formula
formToFormula (Atom v) = Variable v
formToFormula (lhs :&: rhs) = conjunction (formToFormula lhs) (formToFormula rhs)
formToFormula (lhs :|: rhs) = disjunction (formToFormula lhs) (formToFormula rhs)
formToFormula (lhs :=>: rhs) = implication (formToFormula lhs) (formToFormula rhs)
formToFormula (lhs :<=>: rhs) = conjunction (implication lhsFormula rhsFormula) (implication rhsFormula lhsFormula)
  where
    lhsFormula = formToFormula lhs
    rhsFormula = formToFormula rhs

formToFormula TRUE = implication bottom bottom
formToFormula FALSE = bottom

flatClauseToFormula :: Clause -> Formula
flatClauseToFormula (cs :-> ds) =
  implication
    (foldr (conjunction . variable) (variable $ head cs) (tail ds))
    (foldr (disjunction . variable) (variable $ head ds) (tail ds))

implClauseToFormula :: ImplClause -> Formula
implClauseToFormula ((a :-> b) :-> c) = implication (implication (variable a) (variable b)) (variable c)
