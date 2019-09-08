open import Common.IO
open import Common.Unit
open import Common.String
open import Common.Nat

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream public


repeat : Stream String
head repeat = "hello"
tail repeat = repeat

lookup : ∀ {A} → Stream A → Nat → A
lookup xs zero = xs .head
lookup xs (suc n) = lookup (xs .tail) n

main : IO Unit
main = putStr (lookup repeat 1000000)
