{-# LANGUAGE LambdaCase #-}

module SAT where

import qualified Data.Foldable as Foldable
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Traversable as Traversable
import Formula
import Z3.Monad

algorithm :: (MonadZ3 z3) => z3 (Maybe [Bool])
algorithm = do
  vars <- Traversable.sequence $ Map.fromList [("a", mkFreshBoolVar "a"), ("b", mkFreshBoolVar "b"), ("c", mkFreshBoolVar "c")]
  let algorithm' (assertion : assertions) = assertion vars >> algorithm' assertions
      algorithm' [] = fmap snd $ withModel $ \m -> Maybe.catMaybes <$> mapM (evalBool m) (Map.elems vars)

  let modelAssertions =
        [ createAssertion (Disjunction [Variable "a", Variable "b", Variable "c"]),
          createAssertion (Implication [Variable "a", Variable "c"]),
          createAssertion (Variable "a")
        ]

  algorithm' modelAssertions

prove :: Set Formula -> Set Formula -> Formula -> Bool
prove impls flats atom = undefined
  where
    prove' :: (MonadZ3 z3) => z3 ()
    prove' = do
      -- prove
      
      let initClauses = (Set.toList . Set.union flats . Set.map (\case (Implication [Implication [_, x], y]) -> implication x y)) impls

      vars <-
        ( Traversable.sequence
            . Map.fromSet mkFreshBoolVar
            . Foldable.fold
            . map variables
          )
          initClauses

      Foldable.foldr1 (>>) $ map (flip createAssertion vars) initClauses

      return ()

    intuitProve = undefined
    intuitCheck = undefined
