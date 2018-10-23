{-# LANGUAGE OverloadedStrings, OverloadedLists #-}
{-# OPTIONS_GHC -Wall #-}
module Agda.Compiler.Malfunction.Primitive
  ( primitives
  , unitT
  , primitivesCode
  , errorT
  , primCode
  ) where

import Data.Map (Map)

import Agda.Compiler.Malfunction.AST




primitives :: Map String Term
primitives =
  -- Integer functions
  [ "primIntegerPlus"     |-> binOp TBigint Add
  , "primIntegerMinus"    |-> binOp TBigint Sub
  , "primIntegerTimes"    |-> binOp TBigint Mul
  , "primIntegerDiv"      |-> binOp TBigint Div
  , "primIntegerMod"      |-> binOp TBigint Mod
  , "primIntegerEquality" |-> binOp TBigint Eq
  , "primIntegerLess"     |-> binOp TBigint Lt
 , notMapped "primIntegerAbs"
 , notMapped "primNatToInteger"
  , "primShowInteger"     |-> Mglobal ["Z", "to_string"]

  -- Level functions
  , "primLevelZero"       |-> unitT
  , "primLevelSuc"        |-> sucT
  , "primLevelMax"        |-> maxT

  -- Sorts
  , "primSetOmega"        |-> unitT

  
  -- Natural number functions
  , "primNatPlus"         |-> binOp TBigint Add
  , "primNatMinus"        |-> primCode "primNatMinus"
  , "primNatTimes"        |-> binOp TBigint Mul
  , "primNatDivSucAux"    |-> primCode "primNatDivSucAux"
  , "primNatModSucAux"    |-> primCode "primNatModSucAux"
  , "primNatEquality"     |-> binOp TBigint Eq
  , "primNatLess"         |-> binOp TBigint Lt


  -- Floating point functions
 , notMapped "primNatToFloat"
 , notMapped "primFloatPlus"
 , notMapped "primFloatMinus"
 , notMapped "primFloatTimes"
 , notMapped "primFloatNegate"
 , notMapped "primFloatDiv"
  -- ASR (2016-09-29). We use bitwise equality for comparing Double
  -- because Haskell's Eq, which equates 0.0 and -0.0, allows to prove
  -- a contradiction (see Issue #2169).
  , notMapped "primFloatEquality"
  , notMapped "primFloatNumericalEquality"
  , notMapped "primFloatNumericalLess"
  , notMapped "primFloatSqrt"
  , notMapped "primRound"
  , notMapped "primFloor"
  , notMapped "primCeiling"
  , notMapped "primExp"
  , notMapped "primLog"
  , notMapped "primSin"
  , notMapped "primCos"
  , notMapped "primTan"
  , notMapped "primASin"
  , notMapped "primACos"
  , notMapped "primATan"
  , notMapped "primATan2"
  , notMapped "primShowFloat"

  -- Character functions
  , "primCharEquality" |-> primCode "primCharEqual"
  , "primIsLower" |-> primCode "primIsLower"
  , "primIsDigit" |-> primCode "primIsDigit"
  , "primIsAlpha" |-> primCode "primIsAlpha"
  , "primIsSpace" |-> primCode "primIsSpace"
  , "primIsAscii" |-> primCode "isASCII"
  , "primIsLatin1" |-> primCode "primIsLatin"
  , notMapped "primIsPrint"
  , "primIsHexDigit" |-> primCode "primIsHexDigit"
  , "primToUpper" |-> primCode "primToUpper" 
  , "primToLower" |-> primCode "primToLower"
  , "primCharToNat" |-> primCode "primCharToNat"
  , "primNatToChar" |-> primCode "primNatToChar"
  , "primShowChar" |-> primCode "primShowChar"

  -- String functions
  , "primStringToList" |-> primCode "unpack"
  , "primStringFromList" |-> primCode "pack"
  , "primStringAppend" |-> primStringAppend
  , "primStringEquality" |-> primCode "string_equality"
  , "primShowString" |-> primCode "primShowString"


  , notMapped "primQNameEquality"
  , notMapped "primQNameLess"
  , notMapped "primShowQName"
  , notMapped "primQNameFixity"
  , notMapped "primMetaEquality"
  , notMapped "primMetaLess"
  , notMapped "primShowMeta"

  
  -- Other stuff
  , notMapped "primTrustMe"
    -- This needs to be force : A → ((x : A) → B x) → B x rather than seq because of call-by-name.
    -- TODO Check this.
  , notMapped "primForce"
--  , "primForce" |-> Mlambda ["a" , "f"] (Mapply (Mvar "f") [(Mvar "a")])
  , notMapped "primForceLemma"
  
   ]



notMapped :: String -> (String , Term)
notMapped s = (s , errorT (s ++ " : is not supported at the moment."))

(|->) :: a -> b -> (a, b)
(|->) = (,)


binOp :: IntType -> BinaryIntOp -> Term
binOp tp op = Mlambda ["a", "b"] (Mbiop op tp (Mvar "a") (Mvar "b"))

-- | Defines a run-time error in Malfunction - equivalent to @error@ in Haskell.
errorT :: String -> Term
errorT err = Mapply (Mglobal ["Pervasives", "failwith"]) [Mstring err]


unitT :: Term
unitT = Mint $ CInt 0

sucT :: Term
sucT = Mlambda ["a"] unitT
maxT :: Term
maxT = Mlambda ["a" , "b"] unitT


primStringAppend :: Term
primStringAppend = Mglobal ["Pervasives", "^"]

primCode :: String -> Term
primCode s = Mglobal (Longident (Ident "ForeignCode" : Ident "Primitives" : Ident s : []))

primitivesCode :: String
primitivesCode = "\n\
\module Primitives = struct\n\
\\n\
\\n\
\  (* At the edges of those functions (input, output), types are irrelevant because we use \n\
\   * flambda. We consider Char to be equal to Int, because they have the same internal representation.  *)\n\
\\n\
\  \n\
\  let nln = `Readline (Uchar.of_int 0x000A)\n\
\  let utf8 = `UTF_8\n\
\  \n\
\  let unpack s =\n\
\    let rec loop d acc = match Uutf.decode d with\n\
\                   | `End -> List.rev acc\n\
\                   | `Uchar c -> loop d (c :: acc)\n\
\                   | _ -> loop d (Uutf.u_rep :: acc)\n\
\    in loop (Uutf.decoder ~nln:nln ~encoding:utf8 (`String s)) []\n\
\      \n\
\  \n\
\  \n\
\  let pack ls =\n\
\    let buf = Buffer.create ((List.length ls) * 2) in\n\
\    let e = Uutf.encoder utf8 (`Buffer buf)\n\
\    in let rec loop ls = match ls with\n\
\                          | [] -> ignore(Uutf.encode e `End) ; Buffer.contents buf\n\
\                          | (c :: ls) -> ignore (Uutf.encode e (`Uchar c)) ; loop ls\n\
\       in loop ls\n\
\  \n\
\  \n\
\  let nf = `NFC\n\
\  \n\
\  let string_equality s1 s2 =\n\
\    let s11 = Uunf_string.normalize_utf_8 nf s1 in\n\
\    let s22 = Uunf_string.normalize_utf_8 nf s2 in\n\
\    s11 = s22\n\
\    \n\
\  \n\
\  let primCharEqual x y = Uchar.equal x y\n\
\  let primIsLower x = Uucp.Case.is_lower x\n\
\\n\
\  let isASCII b = let x = Uchar.to_int b in (x >= 0) && (x < 256)\n\
\\n\
\  let primIsDigit x = match Uucp.Num.numeric_type x with\n\
\    | `Di -> isASCII x\n\
\    | _ -> false\n\
\\n\
\  let primIsAlpha x = Uucp.Alpha.is_alphabetic x\n\
\\n\
\  let primIsSpace x = let iw = Uucp.White.is_white_space x in\n\
\                      match (isASCII x) with\n\
\    | true -> let i = Uchar.to_int x                           (* \v                      \f *)\n\
\              in (i = 0x9) || (i = 0xA) || (i = 0xD) || (i = 0xB) || (i = 0xC) || iw\n\
\    | false -> iw \n\
\\n\
\  let primIsLatin x = Uchar.is_char x\n\
\\n\
\  let primIsHexDigit x = Uucp.Num.is_ascii_hex_digit x\n\
\\n\
\  let primToLower x = Uucp.Case.Map.to_lower x\n\
\  let primToUpper x = Uucp.Case.Map.to_upper x\n\
\\n\
\  let primCharToNat x = Z.of_int x\n\
\  let primNatToChar x = Z.to_int x\n\
\  let primShowChar x = pack [x]\n\
\  let primShowString s = \"\\\"\" ^ s ^ \"\\\"\"\n\
\\n\
\  let primNatMinus x y = Z.max Z.zero (Z.sub x y)\n\
\  let primNatDivSucAux k m n j = Z.add k (Z.div (Z.max Z.zero (Z.add n (Z.sub m j))) (Z.add m Z.one))\n\
\  let primNatModSucAux k m n j = if Z.gt n j then Z.rem (Z.sub n (Z.add j Z.one)) (Z.add m Z.one) else (Z.add k n)\n\
\end\n"

