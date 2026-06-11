module Refactoring.Lambda.Lambda(module Refactoring.Lambda.Lambda) where

data Lambda_ =
  Abstraction [String] Lambda_ |  -- self reducible
  Const Lambda_ |  -- as abstraction

  Variable String |  -- elim

  Case Lambda_ [(String, Lambda_)] |  -- self reducible
  Sum Int Int Lambda_ |  -- elim

  Product [Lambda_] |  -- elim
  Proj Int Int Lambda_ |  -- self reducible
  Insert Int Int Lambda_ Lambda_|  -- self reducible

  Application [Lambda_] -- unfold

data Substitution_ = Substitution Lambda_ String Lambda_

substitute :: Substitution_ -> Lambda_ 
substitute (Substitution to capture from) = undefined

reduce :: Lambda_ -> Lambda_
reduce (Abstraction [] body) = reduce body
reduce (Abstraction capture body) = Abstraction capture $ reduce body
reduce (Const body) = Const $ reduce body
reduce cs@(Case (Sum c i arg) cases) =
  if c /= length cases
    then cs  -- actually type mismatch and error
    else let (capture, body) = cases !! i
             substitution = Substitution body capture arg
         in reduce $ substitute substitution
reduce ins@(Insert c i (Product terms) arg) =
  if c /= length terms
    then ins  -- actually type mismatch and error
    else let (before, after) = splitAt i terms
         in Product (before ++ arg : after)

reduce (Application (Abstraction (capture : captures) body : arg : terms)) = reduce $
  Application (reduce (Abstraction captures (substitute $ Substitution body capture arg)) : terms)
reduce (Application (Const body : _ : terms)) = reduce $ Application (body : terms)
reduce (Application (Product [] : arg : terms)) = reduce $ Application (arg : terms)

reduce (Application (Application terms : terms')) = reduce $
  Application (terms ++ terms')
reduce (Application (p@(Product _) : terms)) = Application (p : map reduce terms)
reduce (Application (v@(Variable _) : terms)) = Application (v : map reduce terms)
reduce (Application (s@(Sum c i term) : terms)) = Application (s : map reduce terms)
reduce (Application (p@(Proj c i term) : terms)) = Application (p : map reduce terms)

reduce (Application [term]) = reduce term
reduce (Application (term : terms)) = reduce $ Application (reduce term : terms)

reduce x = x

reduce _ = undefined

