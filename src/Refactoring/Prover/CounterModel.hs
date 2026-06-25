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
import Control.Applicative (asum)

data World a = World Int (Set (Annotated_ a Atom_)) [Impl_ a]

data CounterModel_ a = CounterModel {
  reachableTo :: Map Int [Int],
  reachableFrom :: Map Int [Int],
  worlds :: Map Int (World a)
}

newCounterModel :: Ord a => [Annotated_ a Atom_] -> [Impl_ a] -> CounterModel_ a
newCounterModel world impls = CounterModel {
  reachableTo = Map.singleton 0 [],
  reachableFrom = Map.singleton 0 [],
  worlds = Map.singleton 0 (World 0 (Set.fromList world) impls)
}

addWorld :: Ord a => CounterModel_ a -> Int -> [Annotated_ a Atom_] -> [Impl_ a] -> CounterModel_ a
addWorld counterModel worldId as impls = 
  counterModel {
    reachableTo = Map.insert newWorldId reachableToNewWorld (reachableTo counterModel),
    reachableFrom = Map.insert newWorldId [] $ List.foldr (Map.update (Just . (:) newWorldId)) (reachableFrom counterModel) reachableToNewWorld,
    worlds = Map.insert newWorldId newWorld (worlds counterModel)
  }

  where
    newWorldId = Map.size $ worlds counterModel
    newWorld = World newWorldId (Set.fromList as) impls
    reachableToNewWorld = worldId : (reachableTo counterModel ! worldId)

selectWorld :: Ord a => CounterModel_ a -> Maybe (Impl_ a, World a)
selectWorld counterModel = asum [selectWorld' i | i <- (Map.keys (worlds counterModel))]
  where
    selectWorld' worldId = asum [checkImpl' i | i <- implsToCheck] 
      where
        world@(World _ as implsToCheck) = worlds counterModel ! worldId
        reachableFromWorlds = map (worlds counterModel !) (reachableFrom counterModel ! worldId)

        checkImpl' impl@(Impl a b c) = if condition then Nothing else Just (impl, world)
          where
            condition = Set.member a as || 
                    Set.member b as || 
                    Set.member c as || 
                    any (reachableFromPred impl) reachableFromWorlds
            reachableFromPred (Impl a b _) (World _ as _) =
              Set.member a as && not (Set.member b as)

   

    -- selectWorlds' [] = Nothing
    -- selectWorlds' (worldId:t) =
    --   if condition
    --     then selectWorlds' t
    --     else Just world
    --   where
    --     world@(World _ as _) = worlds counterModel ! worldId
    --     reachableFromWorlds = map (worlds counterModel !) (reachableFrom counterModel ! worldId)
    --     condition = Set.member a as || 
    --                 Set.member b as || 
    --                 Set.member c as || 
    --                 any (reachableFromPred impl) reachableFromWorlds

    --     reachableFromPred (Impl a b _) (World _ as _) =
    --       Set.member a as && not (Set.member b as)

instance Buildable (World a) where
  build (World i as _) =  i |+
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
