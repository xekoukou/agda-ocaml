module Primitives = struct


  (* At the edges of those functions (input, output), types are irrelevant because we use 
   * flambda. We consider Char to be equal to Int, because they have the same internal representation.  *)

  
  let nln = `Readline (Uchar.of_int 0x000A)
  let utf8 = `UTF_8
  
  let unpack s =
    let rec loop d acc = match Uutf.decode d with
                   | `End -> List.rev acc
                   | `Uchar c -> loop d (c :: acc)
                   | _ -> loop d (Uutf.u_rep :: acc)
    in loop (Uutf.decoder ~nln:nln ~encoding:utf8 (`String s)) []
      
  
  
  let pack ls =
    let buf = Buffer.create ((List.length ls) * 2) in
    let e = Uutf.encoder utf8 (`Buffer buf)
    in let rec loop ls = match ls with
                          | [] -> ignore(Uutf.encode e `End) ; Buffer.contents buf
                          | (c :: ls) -> ignore (Uutf.encode e (`Uchar c)) ; loop ls
       in loop ls
  
  
  let nf = `NFC
  
  let string_equality s1 s2 =
    let s11 = Uunf_string.normalize_utf_8 nf s1 in
    let s22 = Uunf_string.normalize_utf_8 nf s2 in
    s11 = s22
    
  
  let primCharEqual x y = Uchar.equal x y
  let primIsLower x = Uucp.Case.is_lower x

  let isASCII b = let x = Uchar.to_int b in (x >= 0) && (x < 256)

  let primIsDigit x = match Uucp.Num.numeric_type x with
    | `Di -> isASCII x
    | _ -> false

  let primIsAlpha x = Uucp.Alpha.is_alphabetic x

  let primIsSpace x = let iw = Uucp.White.is_white_space x in
                      match (isASCII x) with
    | true -> let i = Uchar.to_int x                           (* \v                      \f *)
              in (i = 0x9) || (i = 0xA) || (i = 0xD) || (i = 0xB) || (i = 0xC) || iw
    | false -> iw 

  let primIsLatin x = Uchar.is_char x

  let primIsHexDigit x = Uucp.Num.is_ascii_hex_digit x

  let primToLower x = Uucp.Case.Map.to_lower x
  let primToUpper x = Uucp.Case.Map.to_upper x

  let primCharToNat x = Z.of_int x
  let primNatToChar x = Z.to_int x
  let primShowChar x = pack [x]
  let primShowString s = s

  let primNatMinus x y = Z.max Z.zero (Z.sub x y)
  let primNatDivSucAux k m n j = Z.add k (Z.div (Z.max Z.zero (Z.add n (Z.sub m j))) (Z.add m Z.one))
  let primNatModSucAux k m n j = if Z.gt n j then Z.rem (Z.sub n (Z.add j Z.one)) (Z.add m Z.one) else (Z.add k n)
end

