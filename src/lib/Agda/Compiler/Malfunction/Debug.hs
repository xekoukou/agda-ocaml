module Agda.Compiler.Malfunction.Debug
  (
  definitionSummary 
  ) where

import           Prelude hiding ((<>))
import           Agda.Compiler.Backend
import           Agda.Compiler.Common
import           Agda.Main (runAgda)
import           Agda.Utils.Pretty
import           Agda.Utils.Impossible
import           Agda.Interaction.Options
import           Agda.Syntax.Concrete.Name (TopLevelModuleName (..))

import           Agda.Syntax.Common (isIrrelevant)



import           Control.Monad
import           Control.Monad.Extra
import           Control.Monad.Trans
import           Data.List
import           Data.Char
import           Data.Maybe
import           Data.Map                            (Map)
import qualified Data.Map                            as Map
import           Text.Printf
import           System.FilePath.Posix
import           System.Directory
import           System.Process
import qualified Control.Exception as E
import           System.Exit
import           System.IO


import           Agda.Compiler.Malfunction.AST
import qualified Agda.Compiler.Malfunction.Compiler  as C
import           Agda.Compiler.Malfunction.Optimize
import           Agda.Compiler.Malfunction.EraseDefs
import           Agda.Compiler.Malfunction.Pragmas
import           Agda.Compiler.Malfunction.Primitive

-- TODO Needs review.
definitionSummary :: Definition -> TCM ()
definitionSummary def = do
  liftIO (putStrLn ("Summary for: " ++ show q))
  liftIO $ putStrLn $ unlines [
    show (defName def)
      ++ "  (" ++ show (C.qnameNameId q)++ "), " ++ defntype
    ]
  case theDef def of
    Function{} ->
      whenJustM (toTreeless EagerEvaluation q) $
        \tt ->
          liftIO . putStrLn . render
          $  header '=' (show q)
          $$ sect "Treeless (abstract syntax)"    (text . show $ tt)
          $$ sect "Treeless (concrete syntax)"    (pretty tt)
    _ -> return ()
    where
      sect t dc = text t $+$ nest 2 dc $+$ text ""
      header c h = let cs = replicate 15 c
                   in text $ printf "%s %s %s" cs h cs
      q = defName def
      defntype = case theDef def of
        Constructor{}      -> "constructor"
        Primitive{}        -> "primitive"
        Function{}         -> "function"
        Datatype{}         -> "datatype"
        Record{}           -> "record"
        AbstractDefn{}     -> "abstract"
        Axiom{}            -> "axiom"
        GeneralizableVar{} -> error "TODO"
        DataOrRecSig{}     -> error "TODO"

