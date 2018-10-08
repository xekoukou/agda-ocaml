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
import           Agda.Syntax.Concrete.Name (TopLevelModuleName (..))




import           Control.Monad
import           Control.Monad.Extra
import           Control.Monad.Trans
import           Data.Either
import           Data.List
import           Data.Char
import           Data.Map                            (Map)
import qualified Data.Map                            as Map
import           Data.Maybe
import           Text.Printf
import           System.FilePath.Posix
import           System.Directory


import           Agda.Compiler.Malfunction.AST
import qualified Agda.Compiler.Malfunction.Compiler  as Mlf
import           Agda.Compiler.Malfunction.Pragmas
import           Agda.Compiler.Malfunction.Optimize
import           Agda.Compiler.Malfunction.EraseDefs


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
  -> TCM (Mod , ([(TopLevelModuleName , OCamlCode)] , IsMain))
mlfMod allDefs = do
  (eith , ocCode) <- partitionEithers . catMaybes <$> mapM handlePragmas allDefs
  let (rmDefs, sbs) = partitionEithers eith
  env <- Mlf.mkCompilerEnv rmDefs
  bss <- Mlf.compile env rmDefs
  let (im , bs) = eraseB (concat sbs ++ bss)
      rbs = optimizeLetsB bs
  pure (MMod rbs [] , (ocCode , im))
  







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
compileToMLF :: [Definition] -> FilePath -> TCM ([(TopLevelModuleName , OCamlCode)] , IsMain)
compileToMLF defs fp = do
  (modl , (ocCode , im)) <- mlfMod defs
  let modlTxt = prettyShow modl
  liftIO (fp `writeFile` modlTxt)
  pure (ocCode , im) 






handlePragmas :: Definition -> TCM (Maybe (Either (Either Definition [Binding]) (TopLevelModuleName , OCamlCode)))
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
        pure $ Just $ Right ((toTopLevelModuleName . qnameModule) q , code)
        
      -- Compiling Bool
      Datatype{} | Just q == mbool -> do
       -- TODO It seems that the pragma Bool is not necessary for an untyped language.
       -- only the constructors are important.
       -- Of course, one could provide constructors for different data types for True and False
       -- and we would not be able to provide a warning.
                     
        _ <- sequence_ [primTrue, primFalse] -- Just to get the proper error for missing TRUE/FALSE
        Just true  <- getBuiltinName builtinTrue
        Just false <- getBuiltinName builtinFalse
        let ctr = Mlf.nameToIdent true
        let cfl = Mlf.nameToIdent false
        (pure . Just . Left . Right) $ Named ctr (Mglobal (Longident (Ident "ForeignCode" : Ident "trueC" : []))) :
                                        Named cfl (Mglobal (Longident (Ident "ForeignCode" : Ident "falseC" : []))) : [] 


      -- Compiling Inf
      _ | Just q == minf -> genericError "Inf is not supported at the moment."

      -- TODO We probably need to ignore all remaining axioms.
      -- They can only be OCType or unimplemented ones, postulates without a representation.
      Axiom{} -> 
        case pragma of
          Just (OCType _ _) -> pure . error $ "OCType pragma " ++ prettyShow q
          _ -> genericError "There are postulates that have not been defined."

      Primitive{} -> pure $ Just $ Left $ Left def
      Function{} -> pure $ Just $ Left $ Left def
      _ -> pure $ error "Unexpected case in HandlePragmas."








writeCodeToModule :: FilePath -> [(TopLevelModuleName , OCamlCode)] -> TCM ()
writeCodeToModule dir ocCode = do
  let pcode = map (\(m , c) -> (moduleNameParts m , c)) ocCode
  ifs <- map miInterface . Map.elems <$> getVisitedModules
  let fcs = foldr (\i s-> let mfc = (Map.lookup "OCaml" . iForeignCode) i
                          in case mfc of
                              Just c -> s ++ [((moduleNameParts . toTopLevelModuleName . iModuleName) i , intercalate "\n\n" $ reverse $ map getCode c)]
                              _ -> s ) [] ifs
  liftIO ((dir ++ "/ForeignCode.ml") `writeFile` retCode (fcs ++ pcode)) where
    getCode (ForeignCode _ code)  = code
    retCode :: [([String] , OCamlCode)] -> String
    retCode g = let mp = Map.fromList g
                in byModName "" [] mp
                              



splitToMod :: [String] -> Map [String] OCamlCode -> Maybe ([String] , (Map [String] OCamlCode , Map [String] OCamlCode))
splitToMod mn mp = case Map.size mp of
  0 -> Nothing
  _ -> let len = length mn
           s = fst (Map.elemAt 0 mp) !! len
           nmn = s : mn
       in Just (nmn , Map.partitionWithKey (\k _ -> k !! len == s) mp)


addTab :: String -> String -> String
addTab tab str = tab ++ intercalate ("\n" ++ tab) (lines str)


byModName :: String -> [String] -> Map [String] OCamlCode -> String
byModName tab mn mp = let (here , more) = Map.partitionWithKey (\k _ -> length k == length mn) mp
                          s = case splitToMod mn more of
                                Nothing -> ""
                                Just (lmn , (lmp , omp)) -> byModName (tab ++ "  ") lmn lmp ++ byModName tab mn omp
                      in case mn of
                           [] -> s
                           _ -> let (fl : cm) = last mn
                                in tab ++ "module " ++ (toUpper fl : cm) ++ " = struct\n"
                                   ++ addTab tab ((concatMap snd . Map.toList) here) ++ "\n\n"
                                   ++ s ++ "\n" ++ "end\n"
