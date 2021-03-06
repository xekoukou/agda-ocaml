
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat

data Unit : Set where
  c : ⊤ → Nat → ⊤ → Unit

-- Note that the ⊤ arguments get erased and shouldn't be present in
-- the Haskell version of Unit.
{-# FOREIGN GHC data Unit = Unit Integer #-}
{-# COMPILE GHC Unit = data Unit (Unit) #-}

postulate print : Nat → IO ⊤
{-# COMPILE GHC print = print #-}
{-# COMPILE JS  print = function (x) { return function(cb) { process.stdout.write(x + "\n"); cb(0) } } #-}

{-# FOREIGN OCaml 
  let printNat y world = Lwt.return (print_endline (Z.to_string y))
#-}
{-# COMPILE OCaml print = printNat #-}

foo : Unit → IO ⊤
foo (c _ n _) = print n

main : IO ⊤
main = foo (c _ 12345 _)
