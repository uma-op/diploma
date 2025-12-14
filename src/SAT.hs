{-# LANGUAGE LambdaCase #-}

module SAT where

import qualified Data.Foldable as Foldable
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Maybe as Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Traversable as Traversable
import Formula
import Z3.Monad
import Data.Either (Either(..))


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

      let sol :: (MonadZ3 z3) => z3 ()
          sol = Foldable.foldr1 (>>) $ map (`createAssertion` vars) initClauses

      -- intuitProve

      return ()

    intuitProve' :: (MonadZ3 z3) => Map String AST -> z3 () -> [Formula] -> [Formula] -> Formula -> z3 (Either [Formula] (Map String Bool))
    intuitProve' vars sol impls adds atom  = sol >> do
      t0 <- satProve vars sol adds atom
      case t0 of
        Left a' -> return t0
        Right m' -> if intuitCheck' sol impls m' then return t0 else undefined

    intuitCheck' = undefined


satProve :: (MonadZ3 z3) => Map String AST -> z3 () -> [Formula] -> Formula -> z3 (Either [Formula] (Map String Bool))
satProve vars sol additionalClauses atom = sol >> do
  Foldable.foldr1 (>>) $ map (`createAssertion` vars) additionalClauses
  createAssertion (negation atom) vars
  (result, model) <- withModel $ \m -> Map.map Maybe.fromJust <$> mapM (evalBool m) vars
  case result of
    Sat -> return $ Right (Maybe.fromJust model)
    Unsat -> return $ Left []
    Undef -> undefined


algorithm :: (MonadZ3 z3) => z3 (Either [Formula] (Map String Bool), Either [Formula] (Map String Bool)) 
algorithm = do
  vars <- Traversable.sequence $ Map.fromList [("a", mkFreshBoolVar "a"), ("b", mkFreshBoolVar "b"), ("c", mkFreshBoolVar "c")]

  let sol :: (MonadZ3 z3) => z3 ()
      sol = return ()

  let modelAssertions = [ Disjunction [Variable "a", Variable "b", Variable "c"]
                        , Implication [Variable "a", Variable "c"]
                        ]

  let modelAssertionsA = [ variable "c"
                         ]

  let modelAssertionsB = [ variable "a"
                         ]

  let newSol :: (MonadZ3 z3) => z3 ()
      newSol = sol >> Foldable.foldr1 (>>) (map (`createAssertion` vars) modelAssertions)

  resultA <- satProve vars newSol modelAssertionsA (variable "a")
  resultB <- satProve vars newSol modelAssertionsB (variable "b")
  
  return (resultA, resultB)
