module Internal.ParseProblem where

-------------------------------------------------------------------------
-- types

type Name
  = String

data Form
  = Atom Name
  | Form :&: Form
  | Form :|: Form
  | Form :=>: Form
  | Form :<=>: Form
  | TRUE
  | FALSE
 deriving ( Eq, Ord )

instance Show Form where
  show (Atom a)    = a
  show (p :&: q)   = "(" ++ show p ++ " & " ++ show q ++ ")"
  show (p :|: q)   = "(" ++ show p ++ " | " ++ show q ++ ")"
  show (p :=>: q)  = "(" ++ show p ++ " => " ++ show q ++ ")"
  show (p :<=>: q) = "(" ++ show p ++ " <=> " ++ show q ++ ")"
  show TRUE        = "$true"
  show FALSE       = "$false"

