module ParseProblem where

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

nt :: Form -> Form
nt p = p :=>: FALSE

data Input a
  = Input Name Role a
 deriving ( Eq, Ord )

instance Show a => Show (Input a) where
  show (Input name role x) =
    "fof(" ++ name ++ ", " ++ show role ++ ", " ++ show x ++ " )."

data Role
  = Fact
  | Conjecture
 deriving ( Eq, Ord )

instance Show Role where
  show Fact       = "axiom"
  show Conjecture = "conjecture"
