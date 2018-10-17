
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


end 


  module Common = struct

    
    module IO = struct

      let ioReturn _ _ x = x
      let ioBind _ _ _ _ x f = Lazy.force (f x)
      
      let printString y = print_string y

    end


  end

