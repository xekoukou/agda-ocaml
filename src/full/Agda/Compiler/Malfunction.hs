{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
module Agda.Compiler.Malfunction (backend) where

import           Prelude hiding ((<>))
import           Agda.Compiler.Backend
-- import           Agda.Compiler.CallCompiler
import           Agda.Compiler.Common
import           Agda.Utils.Pretty
import           Agda.Interaction.Options
import           Agda.Syntax.Concrete.Name (TopLevelModuleName (..))

import           Agda.Syntax.Common (isIrrelevant)



import           Control.Monad
import           Control.Monad.Extra
import           Control.Monad.Trans
import           Data.List
import           Data.List.Split
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




-- TODO Replace it with throwimpossible.
_IMPOSSIBLE :: a
_IMPOSSIBLE = error "IMPOSSIBLE"


backend :: Backend
backend = Backend backend'

data MlfOptions = Opts
  { optMLF           :: Bool
  , optMLFLib        :: Bool
  , optCallMLF       :: Bool
  , optDebugMLF      :: Bool
  , optOCamlDeps     :: String
  }

defOptions :: MlfOptions
defOptions = Opts
  { optMLF           = False
  , optMLFLib        = False
  , optCallMLF       = True
  , optDebugMLF      = False
  , optOCamlDeps     = "zarith,uucp,uutf,uunf,uunf.string,lwt"
  }


ttFlags :: [OptDescr (Flag MlfOptions)]
ttFlags =
  [ Option [] ["mlf"] (NoArg enable)
    "Use the Malfunction backend."
  , Option [] ["dont-call-mlf"] (NoArg dontCallMLF)
    "Do not call the malfunction compiler on the output file"
  , Option [] ["cmx"] (NoArg onlyCMX)
    "Create a .cmx file instead of an executable."
  , Option [] ["linkpkg"] (ReqArg whichlibs "pkg1,pkg2")
    "Link the specified packages."
  , Option [] ["d"] (NoArg debugMLF)
    "Generate Debugging Information."
  ]
 where
   enable o = pure o{optMLF = True}
   dontCallMLF o = pure o{optCallMLF = False}
   onlyCMX o = pure o{optMLFLib = True}
   whichlibs s o = pure o{optOCamlDeps = optOCamlDeps defOptions ++ "," ++ s}
   debugMLF o = pure o{optDebugMLF = True}
  
-- We do not support separate compilation.
backend' :: Backend' MlfOptions MlfOptions FilePath [Definition] (Maybe Definition)
backend' = Backend' {
  backendName = "malfunction"
  , options = defOptions
  , commandLineFlags = ttFlags
  , isEnabled = optMLF
  -- Checks if there are metas and aborts if so.
  , preCompile = mlfPreCompile
  , postCompile = mlfCompile
  , preModule = \_ _ fp -> pure $ Recompile fp
  , compileDef = \_env _menv def -> mlfCompileDef def
  , postModule = \_ _ _ _ defs -> pure $ catMaybes defs 
  , backendVersion = Just "0.0.1"
  , scopeCheckingSuffices = False
  }

-- Create the treeless Term here, so that we use the pragma options of the file
-- the definition comes from.
mlfCompileDef :: Definition -> TCM (Maybe Definition)
mlfCompileDef def@(Defn{defName = q , defArgInfo = info , defNoCompilation = noC}) | (isIrrelevant info || noC) = do
  reportSDoc "compile.ghc.definition" 10 $
           pure $ text "Not compiling" <+> (pretty q <> text ".")
  pure Nothing
mlfCompileDef def@Defn{defName = q} = do
  case (theDef def) of
    Function{} -> do toTreeless EagerEvaluation q
                     pure ()
    _ -> pure ()
  pure $ Just def


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
        GeneralizableVar{} -> error "Malfunction.definitionSummar: TODO"




  







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

  
  let returnLib = optMLFLib opts
  (mod , exs) <- analyzeCode allDefs returnLib
  
  -- Compile to Mlf
  compileToMLF mod fp
  let fcfp = mdir ++ "/ForeignCode.ml"
  -- Write Foreign Code.
  writeCodeToModule returnLib fcfp

  
  
  -- Perform the Compilation if requested.
  let deps = case returnLib of
        True -> optOCamlDeps opts
        False -> optOCamlDeps opts ++ ",lwt.unix"
  let args_mlf = "malfunction" : "cmx" : fp : []
      fcfpi = replaceExtension fcfp "mli"
      fcfpci = replaceExtension fcfp "cmi"
      fcfpc = replaceExtension fcfp "cmx"
      args_ocamli = "ocamlfind" : "ocamlopt" : "-i" : "-linkpkg" : "-package" : deps : fcfp : ">" : fcfpi : []
      args_ocamlii = "ocamlfind" : "ocamlopt" : "-c" : "-thread" : "-linkpkg" : "-package" : deps : fcfpi : "-o" : fcfpci : []
      args_ocaml = "ocamlfind" : "ocamlopt" : "-c" : "-thread" : "-linkpkg" : "-package" : deps : fcfpi : fcfp : "-o" : fcfpc : []
      doCall = optCallMLF opts
      exec_path = mdir </> show (nameConcrete outputName)
  callCompiler doCall mdir args_ocamli
  callCompiler doCall mdir args_ocamlii
  callCompiler doCall mdir args_ocaml
  case returnLib of
    True -> do
      let mlifp = replaceExtension fp "mli"
          args_mli = "ocamlfind" : "ocamlopt" : "-c" : "-thread" : "-linkpkg" : "-package" : deps : mlifp : []
      writeMLIFile mlifp exs
      callCompiler doCall mdir args_mli
      callCompiler doCall mdir args_mlf
    False -> do
      callCompiler doCall mdir args_mlf
      let fpcmx = replaceExtension fp "cmx"
          args_focaml = "ocamlfind" : "ocamlopt" : "-o" : exec_path : "-thread" : "-linkpkg" : "-package" : deps : fcfpc : fpcmx : []
      callCompiler doCall mdir args_focaml
      
  where
    allDefs :: [Definition]
    allDefs = concat (Map.elems mods)






analyzeCode :: [Definition] -> Bool -> TCM (Mod , [String])
analyzeCode defs rl = do
    agdaMod <- curMName
    (bss , exs) <- C.compile defs
    let (im , bs) = eraseB bss (if rl then Just (map fst exs) else Nothing)
    
    case (im == NotMain) && (not rl) of
      True -> genericError
            ("No main function defined in " ++ (show . pretty) agdaMod ++ " .")
      False -> pure ()
      
    let rbs = optimizeLetsB bs
    pure (MMod rbs (map (Mvar . fst) exs) , map snd exs)




compileToMLF :: Mod -> FilePath -> TCM ()
compileToMLF mod fp = do
  let modlTxt = prettyShow mod
  liftIO (fp `writeFile` modlTxt)




writeMLIFile :: FilePath -> [String] -> TCM ()
writeMLIFile fp ss = liftIO (fp `writeFile` (intercalate "\n" ss))
                              






writeCodeToModule :: Bool -> FilePath -> TCM ()
writeCodeToModule isLib fp = do
  let adCode = case isLib of
        True -> ""
        False -> "let main_run = Lwt_main.run\n\n"
  ifs <- map miInterface . Map.elems <$> getVisitedModules
  let fcs = foldr (\i s-> let mfc = (Map.lookup "OCaml" . iForeignCode) i
                          in case mfc of
                              Just c -> s ++ [((moduleNameParts . toTopLevelModuleName . iModuleName) i , intercalate "\n\n" $ reverse $ map getCode c)]
                              _ -> s ) [] ifs
  liftIO (fp `writeFile` (adCode ++ primitivesCode ++ (retCode fcs))) where
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

callCompiler
  :: Bool
     -- ^ Should we actually call the compiler
  -> FilePath
  -> [String]
     -- ^ Command-line arguments.
  -> TCM ()
callCompiler doCall compile_dir args =
  if doCall then do
    merrors <- callCompiler' compile_dir args
    case merrors of
      Nothing     -> return ()
      Just errors -> typeError (CompilationError errors)
  else
    reportSLn "compile.cmd" 1 $ "NOT calling: " ++ intercalate " " ("malfunction" : args)

-- | Generalisation of @callCompiler@ where the raised exception is
-- returned.
callCompiler'
  :: FilePath
     -- ^ The path to the compiler
  -> [String]
     -- ^ Command-line arguments.
  -> TCM (Maybe String)
callCompiler' compile_dir args = do
  reportSLn "compile.cmd" 1 $ "Calling: " ++ intercalate " " args
  (_, out, err, p) <-
    liftIO $ createProcess
               (shell (intercalate " " ("cd" : compile_dir : "; " : args)))
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



