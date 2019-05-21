
open import Common.IO
open import Common.Nat
open import Common.String
open import Common.Unit

private
  n : Nat
  n = 7

{-# COMPILE OCaml n as val n : Z.t #-}

main : IO Unit
main = do
          putStrLn (natToString n)
