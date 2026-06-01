module Term where

import qualified Data.List as List
import Data.Bifunctor

data Term =
  Abstraction [String] Term |
  Application [Term] |
  Var { varName :: String } |
  Id |
  Sum Int |
  Const Term |
  Case [(Term, Term)] |
  Insert Int |
  Proj Int |
  Product [Term]

instance Show Term where
  show (Abstraction capture body) = "(\\" ++ concat capture ++ "." ++ show body ++ ")"
  show (Application terms) = "(" ++ concatMap show terms ++ ")"
  show (Var vname) = vname
  show Id = "I"
  show (Sum i) = "S(" ++ show i ++ ")"
  show (Proj i) = "P(" ++ show i ++ ")"
  show (Const t) = "K(" ++ show t ++ ")"
  show (Case cs) = "C(" ++ List.intercalate ", " (map show cs) ++ ")"
  show (Insert i) = "In(" ++ show i ++ ")"
  show (Product ts) = "<" ++ List.intercalate "," (show <$> ts) ++ ">"

substitute ::  -- substitute term without unification
  String ->  -- term(variable) name
  Term ->  -- term to substitute
  Term ->  -- the term in which is substituted
  Term
substitute name arg (Abstraction capture body) = Abstraction capture $ substitute name arg body
substitute name arg (Application terms) = Application $ map (substitute name arg) terms
substitute name arg var@(Var termName) = if name == termName then arg else var
substitute name arg gs@(Sum _) = gs
substitute name arg gp@(Proj _) = gp
substitute name arg (Const term) = Const (substitute name arg term)
substitute name arg (Case cs) = Case [(c, substitute name arg b)| (c, b) <- cs]
substitute name arg ins@Insert{} = ins
substitute name arg Id = Id
substitute name arg (Product ts) = Product [substitute name arg e | e <- ts]

reduce :: Term -> Term
reduce (Abstraction [] body) = reduce body
reduce (Abstraction capture1 (Abstraction capture2 body)) = reduce $ Abstraction (capture1 ++ capture2) body
reduce a@(Abstraction [c] (Var vname)) = if c == vname then Id else a
reduce (Abstraction capture body) = Abstraction capture $ reduce body
reduce (Application ts) =
  case map reduce ts of
    [t] -> reduce t
    (Id: t) -> reduce $ Application t
    (Abstraction [c] body: arg: t) -> reduce $ Application (substitute c arg body : t)
    (Abstraction (c:cs) body: arg: t) -> reduce $ Application (Abstraction cs (substitute c arg body): t)
    (Insert 1 : Id : arg : t) -> reduce $ Application (Product [arg]: t)
    (Insert i : Product ts : arg : t) -> reduce $
      Application (let (before, after) = List.splitAt (i - 1) ts in Product (before ++ arg : after) : t)
    (Proj i : Product ts : t) -> reduce $ Application (ts !! (i - 1) : t)
    (Case cs : Application [Sum i, arg] : t) -> reduce $ Application ( let (capture, body) = cs !! (i - 1) in substitute (varName capture) arg body : t)
    (Const arg : _ : t) -> reduce $ Application (arg : t)
    x -> Application x

reduce (Product ts) = Product (reduce <$> ts)
reduce (Case cases) = Case (second reduce <$> cases)
reduce (Const t) = Const (reduce t)

reduce x = x

