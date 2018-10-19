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
  , "primCharEquality" |-> |-> binOp TInt Eq
  , notMapped "primIsLower"
  , notMapped "primIsDigit"
  , notMapped "primIsAlpha"
  , notMapped "primIsSpace"
  , notMapped "primIsAscii"
  , notMapped "primIsLatin1"
  , notMapped "primIsPrint"
  , notMapped "primIsHexDigit"
  , "primToUpper" |-> primCode "primToUpper" 
  , "primToLower" |-> primCode "primToLower"
  , "primCharToNat" |-> primCode "primCharToNat"
  , "primNatToChar" |-> primCode "primNatToChar"
  , notMapped "primShowChar"

  -- String functions
  , "primStringToList" |-> primCode "primStringToList"
  , "primStringFromList" |-> primCode "primStringFromList"
  , "primStringAppend" |-> primStringAppend
  , "primStringEquality" |-> primCode "primStringEquality"
  , "primShowString" |-> primCode "primShowString"

  -- Other stuff
  , notMapped "primTrustMe"
    -- This needs to be force : A → ((x : A) → B x) → B x rather than seq because of call-by-name.
  , notMapped "primForce"
  , notMapped "primForceLemma"
  , notMapped "primQNameEquality"
  , notMapped "primQNameLess"
  , notMapped "primShowQName"
  , notMapped "primQNameFixity"
  , notMapped "primMetaEquality"
  , notMapped "primMetaLess"
  , notMapped "primShowMeta"
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
primitivesCode = "\
\\n\
\module Primitives = struct \n\
\\n\
\  let primCharToNat x = Z.of_int x \n\
\  let primStringToList s = \n\
\    let rec exp i l =\n\
\      if i < 0 then l else exp (i - 1) (s.[i] :: l) in\n\
\    exp (String.length s - 1) [];;\n\
\  let primStringFromList l = \n\
\    let res = String.make (List.length l) '0' in\n\
\    let rec imp i = function\n\
\     | [] -> res\n\
\     | c :: l -> res.[i] <- c; imp (i + 1) l in\n\
\    imp 0 l;;\n\
\  let primShowString s = s\n\
\  let primStringEquality s1 s2 = String.equal s1 s2\n\
\  let primNatToChar x = Z.to_int x\n\
\  let primToLower x = Char.lowercase_ascii x\n\
\  let primToUpper x = Char.uppercase_ascii x\n\
\  let primNatMinus x y = Z.max Z.zero (Z.sub x y)\n\
\  let primNatDivSucAux k m n j = Z.add k (Z.div (Z.max Z.zero (Z.add n (Z.sub m j))) (Z.add m Z.one))\n\
\  let primNatModSucAux k m n j = if Z.gt n j then Z.rem (Z.sub n (Z.add j Z.one)) (Z.add m Z.one) else (Z.add k n)\n\
\\n\
\\n\
\end \n\n\n"
