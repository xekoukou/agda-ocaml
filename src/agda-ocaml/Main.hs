{-# OPTIONS_GHC -Wall #-}
module Main where

import qualified Agda.Compiler.Malfunction as Malfunction

-- | Invokes the agda-compiler with the additional malfunction backend.
main :: IO ()
main = Malfunction.malfunction
