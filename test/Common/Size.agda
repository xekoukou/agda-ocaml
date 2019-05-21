------------------------------------------------------------------------
-- From the Agda standard library
--
-- Sizes for Agda's sized types
------------------------------------------------------------------------

module Common.Size where

{-# BUILTIN SIZEUNIV SizeU #-}
{-# BUILTIN SIZE     Size   #-}
{-# BUILTIN SIZELT   Size<_ #-}
{-# BUILTIN SIZESUC  ↑_     #-}
{-# BUILTIN SIZEINF  ∞      #-}
{-# BUILTIN SIZEMAX  _⊔ˢ_  #-}

{-# FOREIGN OCaml 
  let up _ = ();;
  let inf = ();;
  let union _ _ = ();;
#-}

{-# COMPILE OCaml ↑_     = up    #-}
{-# COMPILE OCaml ∞      = inf   #-}
{-# COMPILE OCaml _⊔ˢ_   = union #-}
