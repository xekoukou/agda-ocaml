module Main where

import System.Process
import System.Directory

main :: IO ()
main = withCurrentDirectory "benchmark/agda-ocaml" $
  callProcess "./run.sh" []
