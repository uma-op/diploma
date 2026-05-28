module CounterModel where

import Data.Map(Map, (!))
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Data.List as List

import World(World)
import qualified World
import qualified Clausify
import qualified Z3.Base as Z3

data CounterModel = CounterModel {
  reachableTo :: Map Int [Int],
  reachableFrom :: Map Int [Int],
  worlds :: Map Int World
}

newCounterModel :: World -> CounterModel
newCounterModel world = CounterModel {
  reachableTo = Map.singleton 0 [],
  reachableFrom = Map.singleton 0 [],
  worlds = Map.singleton 0 world
}

addWorld :: CounterModel -> Int -> World -> CounterModel
addWorld counterModel worldId newWorld = 
  counterModel {
    reachableTo = Map.insert newWorldId reachableToNewWorld (reachableTo counterModel),
    reachableFrom = Map.insert newWorldId [] $ List.foldr (Map.update (Just . (:) newWorldId)) (reachableFrom counterModel) reachableToNewWorld,
    worlds = Map.insert newWorldId newWorld (worlds counterModel)
  }

  where
    newWorldId = Map.size $ worlds counterModel
    reachableToNewWorld = worldId : (reachableTo counterModel ! worldId)

selectWorld :: CounterModel -> Clausify.ImplClauseAST -> Maybe (Int, World)
selectWorld counterModel impl = selectWorlds' [0..(Map.size (worlds counterModel) - 1)]
  where
    selectWorlds' [] = Nothing
    selectWorlds' (worldId:t) = if condition then selectWorlds' t else Just (worldId, world)
      where
        world = worlds counterModel ! worldId
        reachableFromWorlds = map (worlds counterModel !) (reachableFrom counterModel ! worldId)
        condition = Set.member (Clausify.aAST impl) (World.consts world) || 
                    Set.member (Clausify.bAST impl) (World.consts world) || 
                    Set.member (Clausify.cAST impl) (World.consts world) || 
                    any (reachableFromPred impl) reachableFromWorlds

        reachableFromPred impl reachableWorld  = Set.member (Clausify.aAST impl) (World.consts reachableWorld) &&
                                                not (Set.member (Clausify.bAST impl) (World.consts reachableWorld))

getRoot :: CounterModel -> (Int, World)
getRoot counterModel = (0, worlds counterModel ! 0)

counterModelToString :: Z3.Context -> CounterModel -> IO String
counterModelToString context counterModel = do
  worldStrings <- mapM (World.worldAsString context) (worlds counterModel)
  let worldsString = "Worlds:\n" ++ unlines (map show (Map.toAscList worldStrings))
  let reachableFromsString = "ReachableFrom:\n" ++ unlines (map show (Map.toAscList (reachableFrom counterModel)))
  let reachableTosString = "ReachableTo:\n" ++ unlines (map show (Map.toAscList (reachableTo counterModel)))

  return $ worldsString ++ reachableFromsString ++ reachableTosString

