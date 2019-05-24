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


import Agda.Utils.Impossible



type OCamlType = String
type OCamlCode = String



-- | OCaml backend translation pragmas.
data OCamlPragma
  = OCDefn Range OCamlCode
      --  ^ @COMPILE OCaml x = <code>@
      -- Important : We do not check that types correspond to the pragma.
      -- It could lead to undefined behaviors, crashes and all the other goodies.
   | OCNoErasure Range ()
 -- TODO OCExport should simply define the name of a function that is exported to OCaml.
 -- 'f' is the declaration that will be inserted at .mli .
   | OCExport Range OCamlCode
      -- ^ @COMPILE OCaml x as f@
  deriving (Show, Eq)


instance HasRange OCamlPragma where
  getRange (OCDefn   r _)   = r
  getRange (OCExport r _) = r
  getRange (OCNoErasure r _) = r


-- Syntax for OCaml pragmas:
--  OCDefn CODE       "= CODE"
--  OCExport NAME     "as NAME"


parsePragma :: CompilerPragma -> Either String OCamlPragma
parsePragma (CompilerPragma r s) =
  case parse pragmaP s of
    []  -> Left $ "Failed to parse OCaml pragma '" ++ s ++ "'"
    [p] -> Right p
    ps  -> Left $ "Ambiguous parse of pragma '" ++ s ++ "':\n" ++ unlines (map show ps)  -- shouldn't happen
  where
    pragmaP :: ReadP Char OCamlPragma
    pragmaP = choice [defnP , noErasureP , exportP]

    whitespace = many1 (satisfy isSpace)

    wordsP []     = return ()
    wordsP (w:ws) = skipSpaces *> string w *> wordsP ws

    barP = skipSpaces *> char '|'

    -- quite liberal
    isIdent c = isAlphaNum c || elem c "_.':[]"
    isOp c    = not $ isSpace c || elem c "()"
    ocCode  = many1 get -- very liberal

    paren = between (skipSpaces *> char '(') (skipSpaces *> char ')')

    notTypeOrData = do
      s <- look
      guard $ not $ any (`List.isPrefixOf` s) ["type", "data"]

    exportP = OCExport r <$ wordsP ["as"] <* whitespace <*> ocCode
    defnP = OCDefn r <$ wordsP ["="] <* whitespace <* notTypeOrData <*> ocCode
    noErasureP = OCNoErasure r <$ wordsP ["No-Erasure"] <*> skipSpaces


parseOCamlPragma :: CompilerPragma -> TCM OCamlPragma
parseOCamlPragma p = setCurrentRange p $
  case parsePragma p of
    Left err -> genericError err
    Right p -> return p


getOCamlPragma :: QName -> TCM (Maybe OCamlPragma)
getOCamlPragma q = do
  pragma <- traverse parseOCamlPragma =<< getUniqueCompilerPragma "OCaml" q
  def <- getConstInfo q
  setCurrentRange pragma $ pragma <$ sanityCheckPragma def pragma



sanityCheckPragma :: Definition -> Maybe OCamlPragma -> TCM ()
sanityCheckPragma _ Nothing = return ()
sanityCheckPragma def (Just OCDefn{}) =
  case theDef def of
    Axiom{}        -> return ()
    Function{}     -> return ()
    AbstractDefn{} -> __IMPOSSIBLE__
    _              -> typeError $ GenericError "OCaml definitions can only be given for postulates and functions."
sanityCheckPragma def (Just OCExport{}) =
  case theDef def of
    Axiom{}        -> return ()
    Function{}     -> return ()
    AbstractDefn{} -> __IMPOSSIBLE__
    _              -> typeError $ GenericError "Only postulates and functions can be exported."
sanityCheckPragma def (Just OCNoErasure{}) =
  case theDef def of
    Function{}     -> return ()
    Datatype{}     -> return ()
    Record{}       -> return ()
    AbstractDefn{} -> __IMPOSSIBLE__
    _              -> typeError $ GenericError "Only datatypes, records and functions accept the NoErasure pragma."

