module Main where

import Z3.Monad
import SAT

main :: IO ()
main = evalZ3 algorithm >>= \sol -> print sol
