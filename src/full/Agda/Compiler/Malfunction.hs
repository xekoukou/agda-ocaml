{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
module Agda.Compiler.Malfunction (backend) where

import           Prelude hiding ((<>))
import           Agda.Compiler.Backend
import           Agda.Compiler.CallCompiler
import           Agda.Compiler.Common
import           Agda.Utils.Pretty
import           Agda.Interaction.Options
import           Agda.Syntax.Concrete.Name (TopLevelModuleName (..))




import           Control.Monad
import           Control.Monad.Extra
import           Control.Monad.Trans
import           Data.List
import           Data.Char
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
import qualified Agda.Compiler.Malfunction.Compiler  as Mlf
import           Agda.Compiler.Malfunction.Optimize
import           Agda.Compiler.Malfunction.EraseDefs
import           Agda.Compiler.Malfunction.Pragmas
import           Agda.Compiler.Malfunction.Primitive



--TODO Remove
import Debug.Trace


-- TODO Replace it with throwimpossible.
_IMPOSSIBLE :: a
_IMPOSSIBLE = error "IMPOSSIBLE"


backend :: Backend
backend = Backend backend'

data MlfOptions = Opts
  { optMLFCompile    :: Bool
  , optMLFLib        :: Bool
  , optCallMLF       :: Bool
  , optDebugMLF      :: Bool
  , optOCamlDeps     :: String
  }

defOptions :: MlfOptions
defOptions = Opts
  { optMLFCompile    = False
  , optMLFLib        = False
  , optCallMLF       = True
  , optDebugMLF      = False
  , optOCamlDeps     = "zarith"
  }


ttFlags :: [OptDescr (Flag MlfOptions)]
ttFlags =
  [ Option [] ["mlf"] (NoArg enable)
    "Use the Malfunction backend."
  , Option [] ["dont-call-mlf"] (NoArg dontCallMLF)
    "Do not call the malfunction compiler on the output file"
  , Option [] ["cmx"] (NoArg onlyCMX)
    "Create a .cmx file instead of an executable."
  , Option [] ["-linkpkg"] (ReqArg whichlibs "pkg1,pkg2")
    "Link the specified packages."
  , Option [] ["d"] (NoArg debugMLF)
    "Generate Debugging Information."
  ]
 where
   enable o = pure o{optMLFCompile = True}
   dontCallMLF o = pure o{optCallMLF = False}
   onlyCMX o = pure o{optMLFLib = True}
   whichlibs s o = pure o{optOCamlDeps = "zarith" ++ s}
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



-- | Compiles a whole module
mlfMod
  :: [Definition]   -- ^ All visible definitions
  -> TCM (Mod , IsMain)
mlfMod allDefs = do
  bss <- Mlf.compile allDefs
  let (im , bs) = eraseB bss
      rbs = optimizeLetsB bs
  pure (MMod rbs [] , im)
  







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
  im <- compileToMLF allDefs fp
  let fcfp = mdir ++ "/ForeignCode.ml"
  writeCodeToModule fcfp
  let isMain = mappend modIsMain im -- both need to be IsMain

  
  case modIsMain /= isMain of
    True -> genericError
               ("No main function defined in " ++ (show . pretty) agdaMod ++ " . Use --no-main to suppress this warning.")
    False -> pure ()

  let returnLib = case isMain of
             IsMain -> optMLFLib opts
             NotMain -> True
  
  -- Perform the Compilation if requested.

  let args_mlf = ["cmx"] ++ [fp]
      args_ocaml = "ocamlopt" : "-c" : "-linkpkg" : "-package" : (optOCamlDeps opts) : fcfp : []
      doCall = optCallMLF opts
      ocamlopt = "ocamlfind"
      exec_path = mdir </> show (nameConcrete outputName)
  callCompiler doCall ocamlopt args_ocaml
  callMalfunction doCall mdir args_mlf
  case returnLib of
    True -> pure ()
    False -> do
      let fcfpcmx = replaceExtension fcfp "cmx"
          fpcmx = replaceExtension fp "cmx"
          args_focaml = "ocamlopt" : "-o" : exec_path : "-linkpkg" : "-package" : (optOCamlDeps opts) : fcfpcmx : fpcmx : []
      callCompiler doCall ocamlopt args_focaml
      
  where
    allDefs :: [Definition]
    allDefs = concat (Map.elems mods)





compileToMLF :: [Definition] -> FilePath -> TCM IsMain
compileToMLF defs fp = do
  (modl , im) <- mlfMod defs
  let modlTxt = prettyShow modl
  liftIO (fp `writeFile` modlTxt)
  pure im 










writeCodeToModule :: FilePath -> TCM ()
writeCodeToModule fp = do
  ifs <- map miInterface . Map.elems <$> getVisitedModules
  let fcs = foldr (\i s-> let mfc = (Map.lookup "OCaml" . iForeignCode) i
                          in case mfc of
                              Just c -> s ++ [((moduleNameParts . toTopLevelModuleName . iModuleName) i , intercalate "\n\n" $ reverse $ map getCode c)]
                              _ -> s ) [] ifs
  liftIO (fp `writeFile` (primitivesCode ++ (retCode fcs))) where
    getCode (ForeignCode _ code)  = code
    retCode :: [([String] , OCamlCode)] -> String
    retCode g = let mp = Map.fromList g
                in byModName False "" [] mp
                              



splitToMod :: [String] -> Map [String] OCamlCode -> Maybe ([String] , (Map [String] OCamlCode , Map [String] OCamlCode))
splitToMod mn mp = case Map.size mp of
  0 -> Nothing
  _ -> let len = length mn
           s = fst (Map.elemAt 0 mp) !! len
           nmn = s : mn
       in Just (nmn , Map.partitionWithKey (\k _ -> k !! len == s) mp)


addTab :: String -> String -> String
addTab tab str = tab ++ intercalate ("\n" ++ tab) (lines str)


byModName :: Bool -> String -> [String] -> Map [String] OCamlCode -> String
byModName bl tab mn mp = let (here , more) = Map.partitionWithKey (\k _ -> length k == length mn) mp
                             s = case splitToMod mn more of
                                   Nothing -> ""
                                   Just (lmn , (lmp , omp)) -> byModName True (tab ++ "  ") lmn lmp ++ byModName False tab mn omp
                         in case bl of
                              False -> s
                              True -> let (fl : cm) = head mn
                                      in tab ++ "module " ++ (toUpper fl : cm) ++ " = struct\n\n"
                                         ++ addTab (tab ++ "  ") ((concatMap snd . Map.toList) here) ++ "\n"
                                         ++ s ++ "\n" ++ tab ++ "end\n\n"









-- Used for malfunction because it requires to be called from the compile dir.

callMalfunction
  :: Bool
     -- ^ Should we actually call the compiler
  -> FilePath
  -> [String]
     -- ^ Command-line arguments.
  -> TCM ()
callMalfunction doCall compile_dir args =
  if doCall then do
    merrors <- callMalfunction' compile_dir args
    case merrors of
      Nothing     -> return ()
      Just errors -> typeError (CompilationError errors)
  else
    reportSLn "compile.cmd" 1 $ "NOT calling: " ++ intercalate " " ("malfunction" : args)

-- | Generalisation of @callMalfunction@ where the raised exception is
-- returned.
callMalfunction'
  :: FilePath
     -- ^ The path to the compiler
  -> [String]
     -- ^ Command-line arguments.
  -> TCM (Maybe String)
callMalfunction' compile_dir args = do
  reportSLn "compile.cmd" 1 $ "Calling: " ++ intercalate " " ("malfunction" : args)
  (_, out, err, p) <-
    liftIO $ createProcess
               (shell (intercalate " " ("cd" : compile_dir : "; malfunction" : args)))
                  { std_err = CreatePipe
                  , std_out = CreatePipe
                  }

  -- In -v0 mode we throw away any progress information printed to
  -- stdout.
  case out of
    Nothing  -> _IMPOSSIBLE
    Just out -> forkTCM $ do
      -- The handle should be in text mode.
      liftIO $ hSetBinaryMode out False
      progressInfo <- liftIO $ hGetContents out
      mapM_ (reportSLn "compile.output" 1) $ lines progressInfo

  errors <- liftIO $ case err of
    Nothing  -> _IMPOSSIBLE
    Just err -> do
      -- The handle should be in text mode.
      hSetBinaryMode err False
      hGetContents err

  exitcode <- liftIO $ do
    -- Ensure that the output has been read before waiting for the
    -- process.
    _ <- E.evaluate (length errors)
    waitForProcess p

  case exitcode of
    ExitFailure _ -> return $ Just errors
    _ -> return Nothing
