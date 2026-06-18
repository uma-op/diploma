module Refactoring.Lambda.Lambda(module Refactoring.Lambda.Lambda) where

import Data.Foldable

import Fmt
import Refactoring.Utils.Formatting

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

data Substitution_ = Substitution String Lambda_

substitute :: Lambda_ -> Substitution_ -> Lambda_ 
substitute (Abstraction capture' body) (Substitution capture from) =
  Abstraction capture' (substitute body $ Substitution capture from)
substitute (Const body) (Substitution capture from) = Const (substitute body $ Substitution capture from)
substitute (Variable vname) (Substitution capture from) = if capture == vname then from else (Variable vname)
substitute (Case expr cases) (Substitution capture from) =
  Case (substitute expr $ Substitution capture from)
    [ (capture', substitute body' $ Substitution capture from) | (capture', body') <- cases]
substitute (Sum n i e) (Substitution capture from) = Sum n i (substitute e $ Substitution capture from)
substitute (Product ps) (Substitution capture from) = Product [substitute p $ Substitution capture from | p <- ps]
substitute (Proj n i e) (Substitution capture from) = Proj n i (substitute e $ Substitution capture from)
substitute (Insert n i p e) (Substitution capture from) =
  Insert n i (substitute p $ Substitution capture from) (substitute e $ Substitution capture from)
substitute (Application as) (Substitution capture from) = Application [substitute a $ Substitution capture from | a <- as]

selfReducible :: Lambda_ -> Bool
selfReducible (Abstraction [] _) = True
selfReducible _ = undefined

reduce :: Lambda_ -> Lambda_
reduce (Abstraction [] body) = reduce body
reduce (Abstraction capture body) = Abstraction capture $ reduce body
reduce (Const body) = Const $ reduce body
reduce v@(Variable _) = v
reduce cs@(Case e cases) =
  case reduce e of 
    Sum c i arg -> if c /= length cases
                     then error "Wrong case"
                     else let (capture, body) = cases !! (i - 1)
                              substitution = Substitution capture arg
                          in reduce $ substitute body substitution
    t -> Case t [(capture, reduce body) | (capture, body) <- cases]
reduce (Sum n i e) = Sum n i (reduce e)
reduce (Product ps) = Product (reduce <$> ps)
reduce proj@(Proj n i e) =
  case reduce e of
    Product ps -> if n /= length ps
                    then error "Wrong product length"
                    else reduce (ps !! (i - 1))
    t -> Proj n i t

reduce ins@(Insert c i e arg) =
  case reduce e of
    Product ps -> if c /= length ps
                    then error "Wrong pair length insertion"  -- actually type mismatch and error
                    else let (before, after) = splitAt (i - 1) ps
                         in Product (before ++ arg : after)
    t -> Insert c i t (reduce arg)
reduce (Application (Abstraction (capture : captures) body : arg : terms)) = reduce $
  Application (reduce (Abstraction captures (substitute body $ Substitution capture arg)) : terms)

reduce (Application []) = undefined
reduce (Application [term]) = reduce term
reduce (Application (term : hterm : tterms)) = 
  case reduce term of
    Product [] -> reduce $ Application (hterm : tterms)
    Abstraction (capture : captures) body -> reduce $
      Application (Abstraction captures (substitute body $ Substitution capture hterm) : tterms)
    Const body -> reduce $ Application (body : tterms)
    Application ts -> reduce $ Application (ts ++ tterms)
    t -> Application (t : (reduce <$> (hterm : tterms)))

