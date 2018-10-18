module Primitives = struct

  let primCharToNat x = Z.of_int (Char.code x)
  let primStringToList s =
    let rec exp i l =
     if i < 0 then l else exp (i - 1) (s.[i] :: l) in
    exp (String.length s - 1) [];;
  let primStringFromList l = 
    let res = String.make (List.length l) '0' in
    let rec imp i = function
     | [] -> res
     | c :: l -> res.[i] <- c; imp (i + 1) l in
    imp 0 l;;
  let primShowString s = s
  let primStringEquality s1 s2 = String.equal s1 s2
  let primNatToChar x = Char.chr (Z.to_int x)
  let primToLower x = Char.lowercase_ascii x
  let primToUpper x = Char.uppercase_ascii x
  let primNatMinus x y = Z.max Z.zero (Z.sub x y)
  let primNatDivSucAux k m n j = Z.add k (Z.div (Z.max Z.zero (Z.add n (Z.sub m j))) (Z.add m Z.one))
  let primNatModSucAux k m n j = if Z.gt n j then Z.rem (Z.sub n (Z.add j Z.one)) (Z.add m Z.one) else (Z.add k n)
end
