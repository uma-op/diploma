{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Refactoring.Utils.Formatting(module Refactoring.Utils.Formatting) where

import Data.Foldable
import qualified Data.List as List
import Fmt

joinBy :: Buildable a => Builder -> [a] -> Builder
joinBy sep bs = fold $ List.intersperse sep $ build <$> bs

joinByComma :: Buildable a => [a] -> Builder
joinByComma = joinBy ", "

