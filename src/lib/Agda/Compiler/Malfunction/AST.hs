{- |
Module      :  Agda.Compiler.Malfunction.AST
Maintainer  :  Apostolis Xekoukoulotakis

-}
{-# LANGUAGE OverloadedStrings, UndecidableInstances #-}
{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
module Agda.Compiler.Malfunction.AST
  ( IntType(..)
  , IntConst(..)
  , UnaryIntOp(..)
  , BinaryIntOp(..)
  , BlockTag
  , Case(..)
  , Ident(..)
  , Longident(..)
  , Mod(..)
  , Term(..)
  , Binding(..)
  -- NOTE: I don't know which of these is preferable
  --  * Don't re-export anything from Agda.Utils.Pretty
  --  * export a few things (like we do currently)
  --  * Re-export the whole module
  , pretty
  , prettyShow
  , topModNameToLIdent
  ) where

import Data.Int
import Data.Char
-- There does exist a definition of a type-class `Pretty` in the package
-- `pretty` but this is not the one used for Treeless terms, so for consistency,
-- let's go with Agda's choice.
import Agda.Utils.Pretty
import Data.Data (Data, Typeable)
import GHC.Exts (IsList(..), IsString(..))
import Agda.Syntax.Concrete.Name (TopLevelModuleName (..))


-- | The integer types.
data IntType
  = TInt
  | TInt32
  | TInt64
  | TBigint

deriving stock instance Show     IntType
deriving stock instance Eq       IntType
deriving stock instance Ord       IntType
deriving stock instance Data     IntType
deriving stock instance Typeable IntType

data IntConst
  = CInt Int
  | CInt32 Int32
  | CInt64 Int64
  | CBigint Integer

deriving stock instance Show     IntConst
deriving stock instance Eq       IntConst
deriving stock instance Ord       IntConst
deriving stock instance Data     IntConst
deriving stock instance Typeable IntConst

-- | A unary operator.
data UnaryIntOp = Neg | Not

deriving stock instance Show     UnaryIntOp
deriving stock instance Eq       UnaryIntOp
deriving stock instance Ord       UnaryIntOp
deriving stock instance Data     UnaryIntOp
deriving stock instance Typeable UnaryIntOp

-- | A binary operator.
data BinaryIntOp
  = Add | Sub | Mul | Div | Mod | And | Or | Xor | Lsl | Lsr | Asr
  | Lt | Gt | Lte | Gte | Eq

deriving stock instance Show     BinaryIntOp
deriving stock instance Eq       BinaryIntOp
deriving stock instance Ord       BinaryIntOp
deriving stock instance Data     BinaryIntOp
deriving stock instance Typeable BinaryIntOp


-- | A tag used in the construction of $Block@s.
newtype BlockTag = BlockTag Int

deriving newtype instance Num BlockTag

data Case
  -- (tag _)
  = CaseAnyTag
  -- (tag n)
  | CaseTag Int
  -- _
  | CaseAnyInt
  -- n
  | CaseInt Int

deriving stock instance Show     Case
deriving stock instance Eq       Case
deriving stock instance Ord       Case
deriving stock instance Data     Case
deriving stock instance Typeable Case

-- | An identifier used to reference other values in the malfunction module.
newtype Ident = Ident String

deriving stock   instance Show      Ident
deriving stock   instance Eq        Ident
deriving stock   instance Data      Ident
deriving stock   instance Typeable  Ident
deriving newtype instance IsString  Ident
deriving newtype instance Semigroup Ident
deriving newtype instance Monoid    Ident
deriving newtype instance Ord       Ident

-- | A long identifier is used to reference OCaml values (using @Mglobal@).
newtype Longident = Longident [Ident]

deriving stock   instance Show     Longident
deriving stock   instance Eq       Longident
deriving stock   instance Ord       Longident
deriving stock   instance Data     Longident
deriving stock   instance Typeable Longident
deriving newtype instance IsList   Longident


-- | Defines a malfunction module.
data Mod = MMod [Binding] [Term]

deriving stock instance Show     Mod
deriving stock instance Eq       Mod
deriving stock instance Data     Mod
deriving stock instance Typeable Mod

-- | The overall syntax of malfunction terms.
data Term
  = Mvar Ident
  | Mlambda [Ident] Term
  | Mapply Term [Term]
  | Mlet [Binding] Term
  | Mseq [Term]
  | Mint IntConst
  | Mstring String
  | Mglobal Longident
  | Mswitch Term [([Case], Term)]
  -- Integers
  | Muiop UnaryIntOp IntType Term
  | Mbiop BinaryIntOp IntType Term Term
  | Mconvert IntType IntType Term
  -- Blocks
  | Mblock Int [Term]
  | Mfield Int Term
  -- Lazy Evaluation
  | Mlazy Term
  | Mforce Term

deriving stock instance Show     Term
deriving stock instance Eq       Term
deriving stock instance Ord       Term
deriving stock instance Data     Term
deriving stock instance Typeable Term

data Binding
  = Named Ident String Term
  | Recursive [(Ident, (String , Term))]

deriving stock instance Show     Binding
deriving stock instance Eq       Binding
deriving stock instance Ord       Binding
deriving stock instance Data     Binding
deriving stock instance Typeable Binding

textShow :: Show a => a -> Doc
textShow = text . show

nst :: Doc -> Doc
nst = nest 2

(<.>) :: Doc -> Doc -> Doc
a <.> b = a <> "." <> b

level :: Doc -> Doc -> Doc
level a b = sep [ "(" <+> a, nst b, ")" ]

levelPlus :: Doc -> [Doc] -> Doc
levelPlus a bs = sep $ [ "(" <+> a ] ++ map nst bs ++ [")"]

-- This is a list that has no comma or brackets.
prettyList__ :: Pretty a => [ a ] -> Doc
prettyList__ = fsep . map pretty

instance Pretty Mod where
  pretty (MMod bs ts) = levelPlus "module" (map pretty bs ++ [levelPlus "export" (map pretty ts)])
  prettyPrec _ = pretty

instance Pretty Term where
  pretty tt = case tt of
    Mvar i              -> pretty i
    Mlambda is t        -> level ("lambda" <+> parens (hsep (map pretty is))) (pretty t)
    Mapply t ts         -> levelPlus ("apply " <> pretty t) (map pretty ts)
    Mlet bs t           -> level "let" (prettyList__ bs $$ pretty t)
    Mseq ts             -> level "seq" (prettyList__ ts)
    Mint ic             -> pretty ic
    Mstring s           -> textShow s
    Mglobal li          -> parens $ "global" <+> prettyLongident li
    Mswitch t cexps     -> levelPlus ("switch" <+> pretty t) (map prettyCaseExpression cexps)
    -- Integers
    Muiop op tp t0    -> prettyTypedUOp tp op <+> pretty t0
    Mbiop op tp t0 t1 -> levelPlus (prettyTypedBOp tp op) [pretty t0, pretty t1]
    Mconvert tp0 tp1 t0 -> parens $ "convert" <.> pretty tp0 <.> pretty tp1 <+> pretty t0
    -- Blocks
    Mblock i ts         -> level ("block" <+> parens ("tag" <+> pretty i)) (prettyList__ ts)
    Mfield i t0         -> parens $ "field" <+> pretty i <+> pretty t0
  -- lazy evaluation
    Mlazy t             -> parens $ "lazy" <+> pretty t
    Mforce t            -> parens $ "force" <+> pretty t
  prettyPrec _ = pretty

instance Pretty Binding where
  pretty b = case b of
    Named i cn t    -> text ("; " ++ cn ++ "\n") <+> level (pretty i) (pretty t)
    Recursive bs -> levelPlus "rec" (map showIdentTerm bs)
    where
      showIdentTerm :: (Ident, (String , Term)) -> Doc
      showIdentTerm (i, (cn , t)) = text ("; " ++ cn ++ "\n") <+> level (pretty i) (pretty t)

instance Pretty IntConst where
  pretty ic = case ic of
    CInt    i -> pretty i
    CInt32  i -> pretty i <.> "i32"
    CInt64  i -> textShow i <.> "i64"
    CBigint i -> pretty i <.> "ibig"

prettyLongident :: Longident -> Doc
prettyLongident = hsep . map pretty . toList

instance Pretty Ident where
  pretty (Ident i) = text $ ('$':) i

prettyCaseExpression :: ([Case], Term) -> Doc
prettyCaseExpression (cs, t) = level (prettyList__ cs) (pretty t)

instance Pretty Case where
  pretty c = case c of
    CaseAnyTag          -> "(tag _)"
    CaseTag n           -> "(tag " <> pretty n <> ")"
    CaseAnyInt      -> "_"
    CaseInt n       -> pretty n

instance Pretty UnaryIntOp where
  pretty op = case op of
    Neg -> "?"
    Not -> "?"

instance Pretty BinaryIntOp where
  pretty op = case op of
    Add -> "+"
    Sub -> "-"
    Mul -> "*"
    Div -> "/"
    Mod -> "%"
    And -> "&"
    Or  -> "|"
    Xor -> "^"
    Lsl -> "<<"
    Lsr -> ">>"
    Asr -> "a>>"
    Lt  -> "<"
    Gt  -> ">"
    Lte -> "<="
    Gte -> ">="
    Eq  -> "=="



instance Pretty IntType where
  pretty tp = case tp of
    TInt    -> ""
    TInt32  -> ".i32"
    TInt64  -> ".i64"
    TBigint -> ".ibig"



prettyTypedUOp :: IntType -> UnaryIntOp -> Doc
prettyTypedUOp tp op = pretty op <> pretty tp

prettyTypedBOp :: IntType -> BinaryIntOp -> Doc
prettyTypedBOp tp op = pretty op <> pretty tp


topModNameToLIdent :: String -> TopLevelModuleName -> String -> Longident
topModNameToLIdent fc t fn = Longident (Ident fc : g (moduleNameParts t)) where
  g xs = foldr ((:) . Ident . fup) [Ident fn] xs
  fup (x : xs) = toUpper x : xs
  fup [] = []
