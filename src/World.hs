{-# LANGUAGE TupleSections #-}

module World where

import qualified Z3.Base as Z3
import qualified Data.Maybe as Maybe

import Data.Set (Set)
import qualified Data.Set as Set

data World = World {
  model :: Z3.Model,
  consts :: Set Z3.AST
}

worldAsString :: Z3.Context -> World -> IO String
worldAsString context (World model consts) = unwords <$> mapM (Z3.astToString context) (Set.toList consts)

fromModel :: (Z3.FuncDecl -> Z3.AST) -> Z3.Context -> Z3.Model -> IO World
fromModel funcDeclToAST context model = do
  constDecls <- Z3.getConsts context model
  interps <- Maybe.catMaybes <$> mapM (Z3.getConstInterp context model) constDecls
  interpValues <- mapM (Z3.getBool context) interps
  let astToValues = zip (map funcDeclToAST constDecls) interpValues

  putStrLn "From model consts: "
  print =<< sequence [(, value) <$> Z3.astToString context ast | (ast, value) <- astToValues]

  return World { model = model, consts = Set.fromList [ast | (ast, value) <- astToValues, value] }
