module Formula where

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map, (!))
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Maybe as Maybe

import qualified Z3.Monad as Z3

data Formula = Implication [Formula]
             | Conjunction [Formula]
             | Disjunction [Formula]
             | Negation Formula
             | Variable String


variables :: Formula -> Set String
variables (Implication fs) = foldMap variables fs
variables (Conjunction fs) = foldMap variables fs
variables (Disjunction fs) = foldMap variables fs
variables (Negation fs) = variables fs
variables (Variable vname) = Set.singleton vname

createAssertion :: (Z3.MonadZ3 z3) => Formula -> Map String Z3.AST -> z3 ()
createAssertion f vs = Z3.assert =<< createZ3Formula f
  where
    createZ3Formula :: (Z3.MonadZ3 z3) => Formula -> z3 Z3.AST 
    createZ3Formula (Implication fs) = List.foldr foldingFunction f' fs'
      where
        z3Formulae = map createZ3Formula fs
        (fs', f') = (init z3Formulae, last z3Formulae)
      
        foldingFunction :: (Z3.MonadZ3 z3) => z3 Z3.AST -> z3 Z3.AST -> z3 Z3.AST
        foldingFunction e c = do { x <- e; y <- c; Z3.mkImplies x y }

    createZ3Formula (Conjunction fs) = List.foldl' foldingFunction f' fs'
      where
        z3Formulae = map createZ3Formula fs
        (f', fs') = (head z3Formulae, tail z3Formulae)

        foldingFunction :: (Z3.MonadZ3 z3) => z3 Z3.AST -> z3 Z3.AST -> z3 Z3.AST
        foldingFunction c e = do { x <- c; y <- e; Z3.mkAnd [x, y] }

    createZ3Formula (Disjunction fs) = List.foldl' foldingFunction f' fs'
      where
        z3Formulae = map createZ3Formula fs
        (f', fs') = (head z3Formulae, tail z3Formulae)

        foldingFunction :: (Z3.MonadZ3 z3) => z3 Z3.AST -> z3 Z3.AST -> z3 Z3.AST
        foldingFunction c e = do { x <- c; y <- e; Z3.mkOr [x, y] }

    createZ3Formula (Negation f) = Z3.mkNot =<< createZ3Formula f
    createZ3Formula (Variable name) = return $ vs ! name
  

{-
toZ3Script :: (Z3.MonadZ3 z3) => Formula -> ([z3 Z3.AST], z3 ())
toZ3Script f = (Map.elems createVariables, declareVariables >> declareAssertion)
  where
    varNames = variables f

    createVariables :: Z3.MonadZ3 z3 => Map String (z3 Z3.AST)
    createVariables = Set.foldl (\c k -> Map.insert k (Z3.mkFreshBoolVar k) c) Map.empty varNames

    declareVariables :: Z3.MonadZ3 z3 => z3 Z3.AST
    declareVariables = List.foldl (>>) v vs
      where
        (v:vs) = Map.elems createVariables

    declareAssertion :: (Z3.MonadZ3 z3) => z3 ()
    declareAssertion = Z3.assert =<< declareAssertion' f
      where
        declareAssertion' :: (Z3.MonadZ3 z3) => Formula -> z3 Z3.AST
        declareAssertion' (Implication fs') = List.foldr foldingFunction f fs
          where
            (f:fs) = List.map declareAssertion' fs'

            foldingFunction :: (Z3.MonadZ3 z3) => z3 Z3.AST -> z3 Z3.AST -> z3 Z3.AST
            foldingFunction e c = do {x <- e; y <- c; Z3.mkImplies x y}
        declareAssertion' (Conjunction fs') = List.foldl foldingFunction f fs
          where
            (f:fs) = List.map declareAssertion' fs'

            foldingFunction :: (Z3.MonadZ3 z3) => z3 Z3.AST -> z3 Z3.AST -> z3 Z3.AST
            foldingFunction e c = do {x <- e; y <- c; Z3.mkAnd [x, y]}
        declareAssertion' (Disjunction fs') = List.foldl foldingFunction f fs
          where
            (f:fs) = List.map declareAssertion' fs'

            foldingFunction :: (Z3.MonadZ3 z3) => z3 Z3.AST -> z3 Z3.AST -> z3 Z3.AST
            foldingFunction e c = do {x <- e; y <- c; Z3.mkOr [x, y]}
        declareAssertion' (Negation f) = Z3.mkNot =<< (declareAssertion' f)
        declareAssertion' (Variable v) = Maybe.fromJust $ Map.lookup v createVariables
-}
