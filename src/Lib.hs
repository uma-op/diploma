module Lib where

import Z3.Monad

var :: (MonadZ3 z3) => z3 AST
var = mkFreshBoolVar "a"

expr :: (MonadZ3 z3) => z3 ()
expr = assert =<< var
