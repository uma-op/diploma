module Clause where

import qualified Data.Set as Set

import Formula (PlainFormula(..), Formula(..), Atom)
import qualified Formula
import qualified Z3.Base as Z3

data FlatClauseFormula a = FlatClauseFormula {
  conjunctFormulas :: [a],
  disjunctFromulas :: [a]
} deriving (Eq, Ord)

instance Functor FlatClauseFormula where
  fmap func (FlatClauseFormula cs ds) = FlatClauseFormula {
    conjunctFormulas = map func cs,
    disjunctFromulas = map func ds
  }

-- declareFlat :: (Atom -> Z3.AST) -> Z3.Context -> FlatClauseFormula Atom -> IO (FlatClauseFormula Z3.AST)
-- declareFlat universe context clause@(FlatClauseFormula cs ds) = do
--   let csAST = map universe cs
--   let dsAST = map universe ds
--   let resultClause = FlatClauseFormula (zip cs csAST) (zip ds dsAST)
-- 
--   conjencture <- Z3.mkAnd context csAST
--   disjencture <- Z3.mkOr context dsAST
--   resultAST <- Z3.mkImplies context conjencture disjencture 
-- 
--   return (resultClause, resultAST)

data ImplClauseFormula a = ImplClauseFormula {
  a_ :: a, b_ :: a, c_ :: a
} deriving (Eq, Ord)

instance Functor ImplClauseFormula where
  fmap func (ImplClauseFormula a b c) = ImplClauseFormula {
    a_ = func a,
    b_ = func b,
    c_ = func c
  }

declareImpl :: (Atom -> Z3.AST) -> Z3.Context -> ImplClauseFormula Atom -> IO (ImplClauseFormula (Atom, Z3.AST), Z3.AST)
declareImpl universe context clause@(ImplClauseFormula a b c) = do
  let aAST = universe a
  let bAST = universe b
  let cAST = universe c
  let resultClause = ImplClauseFormula (a, aAST) (b, bAST) (c, cAST)

  atob <- Z3.mkImplies context aAST bAST
  resultAST <- Z3.mkImplies context atob cAST
  return (resultClause, resultAST)

flatClauseFromFormula :: PlainFormula -> Maybe (FlatClauseFormula Atom)
flatClauseFromFormula f@(Implication [Conjunction cs, Disjunction ds]) =
  if all Formula.isAtom (cs ++ ds)
    then
      Just FlatClauseFormula {
        conjunctFormulas = map atom cs,
        disjunctFromulas = map atom ds
      }
    else Nothing

flatClauseFromFormula f@(Implication [Conjunction cs, Atom a]) = 
  if all Formula.isAtom cs
    then
      Just FlatClauseFormula {
        conjunctFormulas = map atom cs,
        disjunctFromulas = [a]
      }
    else Nothing

flatClauseFromFormula f@(Implication [Atom a, Disjunction ds]) =
  if all Formula.isAtom ds
    then
      Just FlatClauseFormula {
        conjunctFormulas = [a],
        disjunctFromulas = map atom ds
      }
    else Nothing

flatClauseFromFormula f@(Implication [Atom a, Atom b]) = 
  Just FlatClauseFormula {
    conjunctFormulas = [a],
    disjunctFromulas = [b]
  }

flatClauseFromFormula f@(Disjunction ds) =
  if all Formula.isAtom ds
    then
      Just FlatClauseFormula {
        conjunctFormulas = [],
        disjunctFromulas = map atom ds
      }
    else Nothing

flatClauseFromFormula (Atom a) = Just FlatClauseFormula { conjunctFormulas = [], disjunctFromulas = [a] }

flatClauseFromFormula _ = Nothing

implClauseFromFormula :: PlainFormula -> Maybe (ImplClauseFormula Atom)
implClauseFromFormula f@(Implication [Implication [Atom a, Atom b], Atom c]) = Just $ ImplClauseFormula a b c
implClauseFromFormula _ = Nothing

implImpliesFlat :: ImplClauseFormula Atom -> FlatClauseFormula Atom
implImpliesFlat impl = FlatClauseFormula {
  conjunctFormulas = [b_ impl], disjunctFromulas = [c_ impl]
}

instance Formula a => Formula (FlatClauseFormula a) where
  plain (FlatClauseFormula cs ds) = Implication [Conjunction $ map plain cs, Disjunction $ map plain ds]
  atoms (FlatClauseFormula cs ds) = Set.unions $ map atoms (cs ++ ds)

instance Formula a => Formula (ImplClauseFormula a) where
  plain (ImplClauseFormula a b c) = Implication [Implication [plain a, plain b], plain c]
  atoms (ImplClauseFormula a b c) = Set.unions [atoms a, atoms b, atoms c]
