module Parse where

open import Common.Unit
open import Common.Char    
open import Common.String 
open import Common.List  


open import Common.IO            

parse : List String → List Char → String
parse (e ∷ [])     []               = "ha"
parse (e ∷ [])     (')' ∷ xs)       = "ho"
parse (e ∷ es)     (a   ∷ xs)       = parse (e ∷ es) xs
parse _ _ = "hi"


parseRegExp : String
parseRegExp = parse ("ff" ∷ []) ('a' ∷ [])

main : _
main = do
    let w = parseRegExp
    putStrLn w
