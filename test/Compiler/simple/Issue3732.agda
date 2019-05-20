open import Common.IO
open import Common.Unit
open import Common.String

-- Currently, it is not actually a test.
-- I need a wat to check that Erasure does not happen when it normally would.

{-# FOREIGN OCaml 

type i = 
  | Bar of string;;

#-}


data I : Set where
  bar : String → I

{-# COMPILE OCaml I No-Erasure #-}


showI : I → String
showI (bar x) = x

main : IO Unit
main = putStr (showI (bar "hello")) >>= λ _ → return unit
