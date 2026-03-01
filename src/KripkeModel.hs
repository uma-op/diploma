{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module KripkeModel where

data World where
  World :: { worlds :: [World]
           , valuation :: [String]
           } -> World

deriving instance Show World 

type KripkeModel = World

empty :: KripkeModel
empty = World { worlds = []
              , valuation = []
              }

addWorld :: KripkeModel -> World -> KripkeModel
addWorld m w = m { worlds = w : worlds m }

setValuation :: KripkeModel -> [String] -> KripkeModel
setValuation m v = m { valuation = v }
