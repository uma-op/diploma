module Refactoring.Lambda.Lambda(module Refactoring.Lambda.Lambda) where

import Data.Foldable

import Fmt
import Refactoring.Utils.Formatting
import Refactoring.Utils.Dot


{- 
 - There is irreducible terms
 - proj should be reduced twice
 -
 - -}

data Lambda_ =
  Abstraction [String] Lambda_ |  -- self reducible
  Const Lambda_ |  -- as abstraction

  Variable { varName :: String } |  -- elim

  Case Lambda_ [(String, Lambda_)] |  -- self reducible
  Sum Int Int Lambda_ |  -- elim

  Product [Lambda_] |  -- elim
  Proj Int Int Lambda_ |  -- self reducible
  Insert Int Int Lambda_ Lambda_|  -- self reducible

  Application [Lambda_] -- unfold


instance Buildable Lambda_ where
  build (Abstraction capture body) = "(\\\\" +| joinBy "" capture |+ "." +| body |+ ")"
  build (Const body) = "K(" +| body |+ ")"
  build (Variable vname) = build vname
  build (Case expr cases) = "Case(" +| expr |+ ", " <> fold ["[" +| c |+ "]" +| b |+ "" | (c, b) <- cases] <> ")"
  build (Sum n i e) = "Sum(" +| n |+ ", " +| i |+ ", " +| e |+ ")"
  build (Product es) = "\\<" +| joinByComma es |+ "\\>"
  build (Proj n i e) = "Proj(" +| n |+ ", " +| i |+ ", " +| e |+ ")"
  build (Insert n i p e) = "Insert(" +| n |+ ", " +| i |+ ", " +| p |+ ", " +| e |+ ")"
  build (Application as) = "(" +| joinBy "" as |+ ")"

instance BuildableDot Lambda_ where
  buildDot = build

data Substitution_ = Substitution Lambda_ String Lambda_

substitute :: Substitution_ -> Lambda_ 
substitute (Substitution (Abstraction capture' body) capture from) =
  Abstraction capture' (substitute $ Substitution body capture from)
substitute (Substitution (Const body) capture from) = Const (substitute $ Substitution body capture from)
substitute (Substitution (Variable vname) capture from) = if capture == vname then from else (Variable vname)
substitute (Substitution (Case expr cases) capture from) =
  Case (substitute $ Substitution expr capture from)
    [ (capture', substitute $ Substitution body' capture from) | (capture', body') <- cases]
substitute (Substitution (Sum n i e) capture from) = Sum n i (substitute $ Substitution e capture from)
substitute (Substitution (Product ps) capture from) = Product [substitute $ Substitution p capture from | p <- ps]
substitute (Substitution (Proj n i e) capture from) = Proj n i (substitute $ Substitution e capture from)
substitute (Substitution (Insert n i p e) capture from) =
  Insert n i (substitute $ Substitution p capture from) (substitute $ Substitution e capture from)
substitute (Substitution (Application as) capture from) = Application [substitute $ Substitution a capture from | a <- as]

selfReducible :: Lambda_ -> Bool
selfReducible (Abstraction [] _) = True
selfReducible _ = undefined

reduce :: Lambda_ -> Lambda_
reduce (Abstraction [] body) = reduce body
reduce (Abstraction capture body) = Abstraction capture $ reduce body
reduce (Const body) = Const $ reduce body
reduce cs@(Case (Sum c i arg) cases) =
  if c /= length cases
    then error "Wrong case"  -- actually type mismatch and error
    else let (capture, body) = cases !! (i - 1)
             substitution = Substitution body capture arg
         in reduce $ substitute substitution
reduce cs@(Case e cases) = if selfReducible e then  Case (reduce e) [(capture, reduce body) | (capture, body) <- cases]
reduce proj@(Proj n i (Product ps)) =
  if n /= length ps
    then error "Wrong product length"
    else reduce (ps !! (i - 1))
reduce proj@(Proj n i e) = Proj n i (reduce e)
reduce ins@(Insert c i (Product terms) arg) =
  if c /= length terms
    then error "Wrong pair length insertion"  -- actually type mismatch and error
    else let (before, after) = splitAt i terms
         in Product (before ++ arg : after)
reduce ins@(Insert c i p arg) = Insert c i (reduce p) (reduce arg)

reduce (Application (Abstraction (capture : captures) body : arg : terms)) = reduce $
  Application (reduce (Abstraction captures (substitute $ Substitution body capture arg)) : terms)

reduce (Application (Const body : _ : terms)) = reduce $ Application (body : terms)
reduce (Application (Product [] : arg : terms)) = reduce $ Application (arg : terms)

reduce (Application (Application terms : terms')) = reduce $ Application (terms ++ terms')

reduce (Application (p@(Product _) : terms)) = Application (p : map reduce terms)
reduce (Application (v@(Variable _) : terms)) = Application (v : map reduce terms)
reduce (Application (s@(Sum c i term) : terms)) = Application (s : map reduce terms)
reduce (Application (p@(Proj c i term) : terms)) = Application (p : map reduce terms)

reduce (Application [term]) = reduce term
reduce (Application (term : terms)) = reduce $ Application (reduce term : terms)

reduce x = x

reduce _ = undefined

