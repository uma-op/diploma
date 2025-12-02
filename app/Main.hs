module Main where


import Z3.Monad
import qualified Data.Traversable as Traversable

import Data.Maybe (Maybe(..))
import qualified Data.Maybe as Maybe
import Formula
import qualified Data.Map as Map

algorithm :: (MonadZ3 z3) => z3 (Maybe [Bool])
algorithm = do
  vars <- Traversable.sequence $ Map.fromList [("a", mkFreshBoolVar "a"), ("b", mkFreshBoolVar "b"), ("c", mkFreshBoolVar "c")]
  let algorithm' (assertion:assertions) = assertion vars >> algorithm' assertions
      algorithm' [] = fmap snd $ withModel $ \m -> Maybe.catMaybes <$> mapM (evalBool m) (Map.elems vars)

  let modelAssertions = [ createAssertion (Disjunction [Variable "a", Variable "b", Variable "c"])
                        , createAssertion (Implication [Variable "a", Variable "c"])
                        , createAssertion (Variable "a")]

  algorithm' modelAssertions

main :: IO ()
main = do
  sol <- evalZ3 algorithm
  case sol of 
    Just x -> putStrLn ("Solution" ++ show x)
    Nothing -> putStrLn "not found"
