module Refactoring.Prover.CounterModel(module Refactoring.Prover.CounterModel) where 

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map, (!))
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Foldable as Foldable

import Refactoring.Formula.Atom
import Refactoring.Clause.Impl
import Refactoring.Sequent.Annotated

import Fmt

data World a = World Int (Set (Annotated_ a Atom_))

data CounterModel_ a = CounterModel {
  reachableTo :: Map Int [Int],
  reachableFrom :: Map Int [Int],
  worlds :: Map Int (World a)
}

newCounterModel :: Ord a => [Annotated_ a Atom_] -> CounterModel_ a
newCounterModel world = CounterModel {
  reachableTo = Map.singleton 0 [],
  reachableFrom = Map.singleton 0 [],
  worlds = Map.singleton 0 (World 0 (Set.fromList world))
}

addWorld :: Ord a => CounterModel_ a -> Int -> [Annotated_ a Atom_] -> CounterModel_ a
addWorld counterModel worldId as = 
  counterModel {
    reachableTo = Map.insert newWorldId reachableToNewWorld (reachableTo counterModel),
    reachableFrom = Map.insert newWorldId [] $ List.foldr (Map.update (Just . (:) newWorldId)) (reachableFrom counterModel) reachableToNewWorld,
    worlds = Map.insert newWorldId newWorld (worlds counterModel)
  }

  where
    newWorldId = Map.size $ worlds counterModel
    newWorld = World newWorldId (Set.fromList as)
    reachableToNewWorld = worldId : (reachableTo counterModel ! worldId)

selectWorld :: Ord a => CounterModel_ a -> Impl_ a -> Maybe (World a)
selectWorld counterModel impl@(Impl a b c) = selectWorlds' [0..(Map.size (worlds counterModel) - 1)]
  where
    selectWorlds' [] = Nothing
    selectWorlds' (worldId:t) =
      if condition
        then selectWorlds' t
        else Just world
      where
        world@(World _ as) = worlds counterModel ! worldId
        reachableFromWorlds = map (worlds counterModel !) (reachableFrom counterModel ! worldId)
        condition = Set.member a as || 
                    Set.member b as || 
                    Set.member c as || 
                    any (reachableFromPred impl) reachableFromWorlds

        reachableFromPred (Impl a b _) (World _ as) =
          Set.member a as && not (Set.member b as)

instance Buildable (World a) where
  build (World i as) =  i |+
    " [label=\"{<name>" +| i |+ 
    "|<atoms>" <> unwordsF (annotated <$> Set.toAscList as) <> "}\"]"

instance Buildable (CounterModel_ a) where
  build (CounterModel reachableTo reachableFrom worlds) = 
    "digraph {\n" <>
    "  graph [rankdir=BT]\n" <>
    "  node [shape=record]\n" <>
    indentF 2 (unlinesF $ Map.elems worlds) <>
    indentF 2 (Foldable.fold [ancestor |+ " -> " +| i |+ "\n" | (i, (ancestor: _)) <- Map.toAscList reachableTo]) <>
    "}"
