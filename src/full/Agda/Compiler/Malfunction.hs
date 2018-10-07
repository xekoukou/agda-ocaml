{-# OPTIONS_GHC -Wall #-}
module Agda.Compiler.Malfunction (backend) where

import           Prelude hiding ((<>))
import           Agda.Compiler.Backend
import           Agda.Compiler.CallCompiler
import           Agda.Compiler.Common
import           Agda.Utils.Pretty
import           Agda.Interaction.Options
import           Agda.Syntax.Common (isIrrelevant)
import           Agda.TypeChecking.Primitive (getBuiltinName)
import           Agda.TypeChecking.Monad.Builtin
import           Agda.Utils.Lens
import           Agda.TypeChecking.Warnings




import           Control.Monad
import           Control.Monad.Extra
import           Control.Monad.Trans
import           Data.Either
import           Data.List
import           Data.Map                            (Map)
import qualified Data.Map                            as Map
import           Data.Maybe
import           Text.Printf
import           System.FilePath.Posix
import           System.Directory


import           Agda.Compiler.Malfunction.AST
import qualified Agda.Compiler.Malfunction.Compiler  as Mlf
import           Agda.Compiler.Malfunction.Pragmas


-- TODO Replace it with throwimpossible.
_IMPOSSIBLE :: a
_IMPOSSIBLE = error "IMPOSSIBLE"


backend :: Backend
backend = Backend backend'

data MlfOptions = Opts
  { optMLFCompile    :: Bool
  , optCallMLF       :: Bool
  , optDebugMLF      :: Bool
  }

defOptions :: MlfOptions
defOptions = Opts
  { optMLFCompile    = False
  , optCallMLF       = True
  , optDebugMLF      = False
  }


ttFlags :: [OptDescr (Flag MlfOptions)]
ttFlags =
  [ Option [] ["mlf"] (NoArg enable)
    "Generate Malfunction"
  , Option [] ["dont-call-mlf"] (NoArg dontCallMLF)
    "Runs the malfunction compiler on the output file"
  , Option [] ["d"] (NoArg debugMLF)
    "Generate Debugging Information."
  ]
 where
   enable o = pure o{optMLFCompile = True}
   dontCallMLF o = pure o{optCallMLF = False}
   debugMLF o = pure o{optDebugMLF = True}
  
-- We do not support separate compilation.
backend' :: Backend' MlfOptions MlfOptions FilePath [Definition] Definition
backend' = Backend' {
  backendName = "malfunction"
  , options = defOptions
  , commandLineFlags = ttFlags
  , isEnabled = optMLFCompile
  -- Checks if there are metas and aborts if so.
  , preCompile = mlfPreCompile
  , postCompile = mlfCompile
  , preModule = \_ _ fp -> pure $ Recompile fp
  , compileDef = \_env _menv def -> return def
  , postModule = \_ _ _ _ defs -> pure defs 
  , backendVersion = Just "0.0.1"
  , scopeCheckingSuffices = False
  }



mlfPreCompile :: MlfOptions -> TCM MlfOptions
mlfPreCompile mlfOpts = do
  allowUnsolved <- optAllowUnsolved <$> pragmaOptions
  when allowUnsolved $ genericError "Unsolved meta variables are not allowed when compiling."
  return mlfOpts




-- TODO Needs review.
definitionSummary :: MlfOptions -> Definition -> TCM ()
definitionSummary opts def = when (optDebugMLF opts) $ do
  liftIO (putStrLn ("Summary for: " ++ show q))
  liftIO $ putStrLn $ unlines [
    show (defName def)
      ++ "  (" ++ show (Mlf.qnameNameId q)++ "), " ++ defntype
    ]
  case theDef def of
    Function{} ->
      whenJustM (toTreeless q) $
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
        GeneralizableVar{} -> error "Malfunction.definitionSummar: TODO"



-- TODO: Maybe we'd like to refactor this so that we first do something like
-- this (in the calling function)
--
--    partition [Definition] -> ([Function], [Primitive], ...)
--
-- And then we can simply do the topologic sorting stuff on the functions only.
-- This would certainly make this funciton a helluva lot cleaner.
--
-- | Compiles a whole module
mlfMod
  :: [Definition]   -- ^ All visible definitions
  -> TCM (Mod , (OCamlCode , IsMain))
mlfMod allDefs = do
-- TODO We need to use ocCode.
  (rmDefs , ocCode) <- partitionEithers . catMaybes <$> mapM handlePragmas allDefs
  env <- Mlf.mkCompilerEnv rmDefs
  (bs , im) <- Mlf.compile env rmDefs
  pure (MMod bs [] , (concat ocCode , im))
  







-- TODO I need to clean this.
outFile :: [ Name ] -> TCM (FilePath, FilePath , FilePath)
outFile m = do
  mdir <- compileDir
  let (fdir, fn) = let r = map (show . pretty) m
                   in (init r , last r)
  let dir = intercalate "/" (mdir : fdir)
      fp  = dir ++ "/" ++ replaceExtension fn "mlf"
  liftIO $ createDirectoryIfMissing True dir
  return (mdir, dir , fp)



mlfCompile :: MlfOptions -> IsMain -> Map ModuleName [Definition] -> TCM ()
mlfCompile opts modIsMain mods = do
  agdaMod <- curMName
  let outputName = case mnameToList agdaMod of
                    [] -> error "Impossible"
                    ms -> last ms
  (mdir , dir , fp) <- outFile (mnameToList agdaMod)

  -- TODO review ?? Report debugging Information 
  mapM_ (definitionSummary opts) allDefs

  
  -- Perform the transformation to malfunction
  (ocCode , im) <- compileToMLF allDefs fp
  writeCodeToModule dir ocCode
  let isMain = mappend modIsMain im -- both need to be IsMain

  
  case modIsMain /= isMain of
    True -> genericError
               ("No main function defined in " ++ (show . pretty) agdaMod ++ " . Use --no-main to suppress this warning.")
    False -> pure ()

  let op = case isMain of
             IsMain -> "compile"
             NotMain -> "cmx"
  
  -- Perform the Compilation if requested.
  
  let args = [op] ++ [fp] ++ (if isMain == IsMain then ["-o", mdir </> show (nameConcrete outputName)] else [])
  let doCall = optCallMLF opts
      compiler = "malfunction"
  callCompiler doCall compiler args
  where
    allDefs :: [Definition]
    allDefs = concat (Map.elems mods)



--

-- TODO: `Definition`'s should be sorted *and* grouped by `defMutual` (a field
-- in Definition). each group should compile to:
--
--    (rec
--       x0 = def0
--       ...
--    )
compileToMLF :: [Definition] -> FilePath -> TCM (OCamlCode , IsMain)
compileToMLF defs fp = do
  (modl , (ocCode , im)) <- mlfMod defs
  let modlTxt = prettyShow modl
  liftIO (fp `writeFile` modlTxt)
  pure (ocCode , im) 






handlePragmas :: Definition -> TCM (Maybe (Either Definition OCamlCode))
handlePragmas Defn{defArgInfo = info, defName = q} | isIrrelevant info = do
  reportSDoc "compile.ghc.definition" 10 $
           pure $ text "Not compiling" <+> (pretty q <> text ".")
  pure Nothing
handlePragmas def@Defn{defName = q , theDef = d} = do
  reportSDoc "compile.ghc.definition" 10 $ pure $ vcat
    [ text "Compiling" <+> pretty q <> text ":"
    , nest 2 $ text (show d)
    ]
  pragma <- getOCamlPragma q
  mbool  <- getBuiltinName builtinBool
-- We do not need to use mlist. It seems that the haskell backend does that to increase performance.
--  mlist  <- getBuiltinName builtinList
  minf   <- getBuiltinName builtinInf
  mflat  <- getBuiltinName builtinFlat
  case d of
      _ | Just OCDefn{} <- pragma, Just q == mflat ->
        genericError
          "\"COMPILE GHC\" pragmas are not allowed for the FLAT builtin."

      _ | Just (OCDefn r oc) <- pragma -> setCurrentRange r $ do
            
        -- Check that the function isn't INLINE (since that will make this
        -- definition pointless).
        inline <- (^. funInline) . theDef <$> getConstInfo q
        when inline $ warning $ UselessInline q
        -- TODO At the moment we do not check that the type of the OCaml function corresponds to the
        -- type of the agda function or the postulate.
        let code = "let " ++ prettyShow (Mlf.nameToIdent q) ++ " = \n" ++ oc
        pure $ Just $ Right code
        
      -- Compiling Bool
      Datatype{} | Just q == mbool -> do
       -- TODO It seems that the pragma Bool is not necessary for an untyped language.
       -- only the constructors are important.
       -- Of course, one could provide constructors for different data types for True and False
       -- and we would not be able to provide a warning.
                     
        _ <- sequence_ [primTrue, primFalse] -- Just to get the proper error for missing TRUE/FALSE
        Just true  <- getBuiltinName builtinTrue
        Just false <- getBuiltinName builtinFalse
        let ctr = "let " ++ prettyShow (Mlf.nameToIdent true) ++ " = true;;"
        let cfl = "let " ++ prettyShow  (Mlf.nameToIdent false) ++ " = false;;"
        pure $ Just $ Right ("\n" ++ ctr ++ "\n" ++ cfl ++ "\n")


      -- Compiling Inf
      _ | Just q == minf -> genericError "Inf is not supported at the moment."

      -- TODO We probably need to ignore all remaining axioms.
      -- They can only be OCType or unimplemented ones, postulates without a representation.
      Axiom{} -> 
        case pragma of
          Just (OCType _ _) -> pure Nothing
          _ -> genericError "There are postulates that have not been defined."

      Primitive{} -> pure $ Just $ Left def
      Function{} -> pure $ Just $ Left def
      _ -> pure $ error "Unexpected case in HandlePragmas."








writeCodeToModule :: FilePath -> OCamlCode -> TCM ()
writeCodeToModule dir ocCode = do
  ifs <- map miInterface . Map.elems <$> getVisitedModules
  let fcs = foldr (\i s-> let mfc = (Map.lookup "OCaml" . iForeignCode) i
                          in case mfc of
                               Just c -> s ++ [c]
                               _ -> s ) [] ifs
  liftIO ((dir ++ "/FC.ml") `writeFile` (concatMap someCode fcs ++ "\n\n" ++ ocCode)) where
    getCode (ForeignCode _ code)  = code
    someCode :: [ForeignCode] -> String
    someCode fc = intercalate "\n\n" $ reverse $ map getCode fc
