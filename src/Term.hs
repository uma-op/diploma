module Term where

data Term =
  Abstraction [String] Term |
  Application [Term] |
  Var { varName :: String } |
  Id |
  GetSum Int Int |
  GetProduct Int Int |
  Const Term |
  Case Term [(Term, Term)] |
  Insert Int Int
  deriving Show

substitute ::  -- substitute term without unification
  String ->  -- term(variable) name
  Term ->  -- term to substitute
  Term ->  -- the term in which is substituted
  Term
substitute name arg (Abstraction capture body) = Abstraction capture $ substitute name arg body
substitute name arg (Application terms) = Application $ map (substitute name arg) terms
substitute name arg var@(Var termName) = if name == termName then arg else var
substitute name arg gs@(GetSum _ _) = gs
substitute name arg gp@(GetProduct _ _) = gp
substitute name arg (Const term) = Const (substitute name arg term)
substitute name arg (Case e cs) = Case (substitute name arg e) [(c, substitute name arg b)| (c, b) <- cs]
substitute name arg ins@Insert{} = ins
substitute name arg Id = Id

