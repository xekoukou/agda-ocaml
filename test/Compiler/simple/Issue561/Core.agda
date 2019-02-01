module Issue561.Core where

postulate
  Char : Set

{-# BUILTIN CHAR Char #-}

open import Agda.Builtin.IO public

postulate
  return  : ∀ {a} {A : Set a} → A → IO A

{-# COMPILE GHC return = \_ _ -> return #-}
{-# COMPILE UHC return = \_ _ x -> UHC.Agda.Builtins.primReturn x #-}
{-# COMPILE JS return =
    function(u0) { return function(u1) { return function(x) { return function(cb) { cb(x); }; }; }; } #-}
{-# FOREIGN OCaml
  let ioReturn _ _ x world = Lwt.return x
  let ioBind _ _ _ _ x f world = Lwt.bind (x world) (fun x -> f x world)
#-}

{-# COMPILE OCaml return = ioReturn #-}
