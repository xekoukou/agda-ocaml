{-# LANGUAGE CPP #-}
module Agda.Compiler.Malfunction.Pragmas where



import Control.Monad
import Data.Maybe
import Data.Char
import qualified Data.List as List
import Data.Traversable (traverse)
import Data.Map (Map)
import qualified Data.Map as Map

import Agda.Syntax.Position
import Agda.Syntax.Abstract.Name
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Primitive

import Agda.Utils.Lens
import Agda.Utils.Parser.ReadP
import Agda.Utils.Pretty hiding (char)
import Agda.Utils.String ( ltrim )
import Agda.Utils.Three

import Agda.Compiler.Common

import Agda.Utils.Impossible



type OCamlType = String
type OCamlCode = String



-- | GHC backend translation pragmas.
data OCamlPragma
  = OCDefn Range OCamlCode
      --  ^ @COMPILE OCaml x = <code>@
  | OCType Range OCamlType
      --  ^ @COMPILE OCaml X = type <type>@
--   | OCData Range OCamlType [OCamlCode]
--       -- ^ @COMPILE OCaml X = data D (c₁ | ... | cₙ)
--   | OCExport Range OCamlCode
--       -- ^ @COMPILE OCaml x as f@
  deriving (Show, Eq)


instance HasRange OCamlPragma where
  getRange (OCDefn   r _)   = r
  getRange (OCType   r _)   = r
--   getRange (OCData   r _ _) = r
--   getRange (OCExport r _) = r


-- Syntax for OCaml pragmas:
--  OCDefn CODE       "= CODE"
--  OCType TYPE       "= type TYPE"
--  OCData NAME CONS  "= data NAME (CON₁ | .. | CONₙ)"
--  OCExport NAME     "as NAME"


parsePragma :: CompilerPragma -> Either String OCamlPragma
parsePragma (CompilerPragma r s) =
  case parse pragmaP s of
    []  -> Left $ "Failed to parse OCaml pragma '" ++ s ++ "'"
    [p] -> Right p
    ps  -> Left $ "Ambiguous parse of pragma '" ++ s ++ "':\n" ++ unlines (map show ps)  -- shouldn't happen
  where
    pragmaP :: ReadP Char OCamlPragma
    pragmaP = choice [ typeP, defnP ] -- choice [ exportP, typeP, dataP, defnP ]

    whitespace = many1 (satisfy isSpace)

    wordsP []     = return ()
    wordsP (w:ws) = skipSpaces *> string w *> wordsP ws

    barP = skipSpaces *> char '|'

    -- quite liberal
    isIdent c = isAlphaNum c || elem c "_.':[]"
    isOp c    = not $ isSpace c || elem c "()"
    ocIdent = fst <$> gather (choice
                [ string "()"
                , many1 (satisfy isIdent)
                , between (char '(') (char ')') (many1 (satisfy isOp))
                ])
    ocCode  = many1 get -- very liberal

    paren = between (skipSpaces *> char '(') (skipSpaces *> char ')')

    notTypeOrData = do
      s <- look
      guard $ not $ any (`List.isPrefixOf` s) ["type", "data"]

--     exportP = OCExport r <$ wordsP ["as"]        <* whitespace <*> ocIdent <* skipSpaces
    typeP   = OCType   r <$ wordsP ["=", "type"] <* whitespace <*> ocCode
--     dataP   = OCData   r <$ wordsP ["=", "data"] <* whitespace <*> ocIdent <*>
--                                                     paren (sepBy (skipSpaces *> ocIdent) barP) <* skipSpaces
    defnP = OCDefn r <$ wordsP ["="] <* whitespace <* notTypeOrData <*> ocCode



parseOCamlPragma :: CompilerPragma -> TCM OCamlPragma
parseOCamlPragma p = setCurrentRange p $
  case parsePragma p of
    Left err -> genericError err
    Right p -> return p


getOCamlPragma :: QName -> TCM (Maybe OCamlPragma)
getOCamlPragma q = do
  pragma <- traverse parseOCamlPragma =<< getUniqueCompilerPragma ghcBackendName q
  def <- getConstInfo q
  setCurrentRange pragma $ pragma <$ sanityCheckPragma def pragma



sanityCheckPragma :: Definition -> Maybe OCamlPragma -> TCM ()
sanityCheckPragma _ Nothing = return ()
sanityCheckPragma def (Just OCDefn{}) =
  case theDef def of
    Axiom{}        -> return ()
    Function{}     -> return ()
    AbstractDefn{} -> pure $ throwImpossible (Impossible __FILE__ __LINE__)
    Datatype{}     -> recOrDataErr "data"
    Record{}       -> recOrDataErr "record"
    _              -> typeError $ GenericError "OCaml definitions can only be given for postulates and functions."
    where
      recOrDataErr which =
        typeError $ GenericDocError $
          sep [ text $ "Bad COMPILE OCaml pragma for " ++ which ++ " type. Use"
              , text "{-# COMPILE OCaml <Name> = data <OCData> (<OCCon1> | .. | <OCConN>) #-}" ]
-- sanityCheckPragma def (Just OCData{}) =
--   case theDef def of
--     Datatype{} -> return ()
--     Record{}   -> return ()
--     _          -> typeError $ GenericError "OCaml data types can only be given for data or record types."
sanityCheckPragma def (Just OCType{}) =
  case theDef def of
    Axiom{} -> return ()
    Datatype{} -> do
      -- We use OCType pragmas for Nat, Int and Bool
      nat  <- getBuiltinName builtinNat
      int  <- getBuiltinName builtinInteger
      bool <- getBuiltinName builtinBool
      unless (Just (defName def) `elem` [nat, int, bool]) err
    _ -> err
  where
    err = typeError $ GenericError "OCaml types can only be given for postulates."
-- sanityCheckPragma def (Just OCExport{}) =
--   case theDef def of
--     Function{} -> return ()
--     _ -> typeError $ GenericError "Only functions can be exported to OCaml using {-# COMPILE OCaml <Name> as <OCName> #-}"
-- 


-- | Get content of @FOREIGN OCaml@ pragmas.
foreignOCaml :: TCM [String]
foreignOCaml =  map getCode . fromMaybe [] . Map.lookup ghcBackendName . iForeignCode <$> curIF
  where getCode (ForeignCode _ code) = code
