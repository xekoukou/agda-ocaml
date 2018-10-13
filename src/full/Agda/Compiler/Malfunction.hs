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


import           Agda.Compiler.Malfunction.AST
import qualified Agda.Compiler.Malfunction.Compiler  as Mlf
import           Agda.Compiler.Malfunction.Optimize
import           Agda.Compiler.Malfunction.EraseDefs
import           Agda.Compiler.Malfunction.Pragmas




--TODO Remove
import Debug.Trace


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
  writeCodeToModule dir
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





compileToMLF :: [Definition] -> FilePath -> TCM IsMain
compileToMLF defs fp = do
  (modl , im) <- mlfMod defs
  let modlTxt = prettyShow modl
  liftIO (fp `writeFile` modlTxt)
  pure im 










writeCodeToModule :: FilePath -> TCM ()
writeCodeToModule dir = do
  ifs <- map miInterface . Map.elems <$> getVisitedModules
  let fcs = foldr (\i s-> let mfc = (Map.lookup "OCaml" . iForeignCode) i
                          in case mfc of
                              Just c -> s ++ [((moduleNameParts . toTopLevelModuleName . iModuleName) i , intercalate "\n\n" $ reverse $ map getCode c)]
                              _ -> s ) [] ifs
  liftIO ((dir ++ "/ForeignCode.ml") `writeFile` retCode fcs) where
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
