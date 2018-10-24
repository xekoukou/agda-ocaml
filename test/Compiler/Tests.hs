{-# LANGUAGE DoAndIfThenElse      #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE PatternGuards        #-}

module Compiler.Tests where

import Utils
import Test.Tasty
import Test.Tasty.Silver.Advanced (readFileMaybe)
import Test.Tasty.Silver
import Test.Tasty.Silver.Filter
import qualified Data.Text as T
import Data.Text.Encoding
import Data.Monoid
import Data.List
import System.Directory
import System.IO.Temp
import System.FilePath
import System.Environment
import System.Exit
import System.Process.Text as PT

import Control.Monad (forM)
import Data.Maybe

import Debug.Trace

type GHCArgs = [String]

data ExecResult
  = CompileFailed
    { result :: ProgramResult }
  | CompileSucceeded
    { result :: ProgramResult }
  | ExecutedProg
    { result :: ProgramResult }
  deriving (Show, Read, Eq)

data Compiler = MAlonzo | JS | OCaml
  deriving (Show, Read, Eq)

data CompilerOptions
  = CompilerOptions
    { extraAgdaArgs :: AgdaArgs
    } deriving (Show, Read)

data TestOptions
  = TestOptions
    { forCompilers   :: [(Compiler, CompilerOptions)]
    , runtimeOptions :: [String]
    , executeProg    :: Bool
    } deriving (Show, Read)

allCompilers :: [Compiler]
allCompilers = [OCaml]

defaultOptions :: TestOptions
defaultOptions = TestOptions
  { forCompilers   = [ (c, co) | c <- allCompilers ]
  , runtimeOptions = []
  , executeProg    = True
  }
  where co = CompilerOptions []

disabledTests :: [RegexFilter]
disabledTests =
  [ -- The Ocaml backend always checks that all postulates have pragmas.
    RFInclude "Compiler/OCaml/simple/Irrelevant"
  , RFInclude "Compiler/.*/simple/Sharing" -- See issue 1528
  , RFInclude "Compiler/OCaml/simple/Issue2821"    -- GHC backend specific
  , RFInclude "Compiler/OCaml/simple/Issue2914"    -- GHC backend specific
    -- Fix to 2524 is too unsafe
  , RFInclude "Compiler/.*/simple/Issue2524"
    -- The following test cases are GHC backend specific.
  , RFInclude "Compiler/OCaml/simple/Issue2879-.*"
  , RFInclude "Compiler/OCaml/simple/Issue2909-.*"
  , RFInclude "Compiler/OCaml/simple/Issue2918"

  -- Temporarily Disabled TODO Enable them.
  
  , RFInclude "Compiler/OCaml/simple/Coind"
  , RFInclude "Compiler/OCaml/simple/CompilingCoinduction"
  , RFInclude "Compiler/OCaml/simple/CompilingQNamePats"
  , RFInclude "Compiler/OCaml/simple/CopatternStreamSized"
  , RFInclude "Compiler/OCaml/simple/Floats"
  , RFInclude "Compiler/OCaml/simple/FloatsUHCFails"
  , RFInclude "Compiler/OCaml/simple/Issue1486"
  , RFInclude "Compiler/OCaml/simple/Issue1664"
  , RFInclude "Compiler/OCaml/simple/Issue1855"
  , RFInclude "Compiler/OCaml/simple/Issue2218"
  , RFInclude "Compiler/OCaml/simple/Issue326"
  , RFInclude "Compiler/OCaml/simple/Literals"
  , RFInclude "Compiler/OCaml/simple/QNameOrder"
  , RFInclude "Compiler/OCaml/simple/Word"
  
  ]

tests :: IO TestTree
tests = do
  let enabledCompilers = [OCaml]

  ts <- mapM forComp enabledCompilers
  return $ testGroup "Compiler" ts
  where
    forComp comp = testGroup (show comp) . catMaybes
        <$> sequence
            [ Just <$> simpleTests comp
            , Just <$> stdlibTests comp
            , specialTests comp]

simpleTests :: Compiler -> IO TestTree
simpleTests comp = do
  let testDir = "test" </> "Compiler" </> "simple"
  inps <- getAgdaFilesInDir NonRec testDir
  tests' <- forM inps $ \inp -> do
    opts <- readOptions inp
    return $
      agdaRunProgGoldenTest testDir comp
        (return $ ["-i" ++ testDir, "-itest/"] ++ compArgs comp) inp opts
  return $ testGroup "simple" $ catMaybes tests'

  where compArgs :: Compiler -> AgdaArgs
        compArgs OCaml = []
        compArgs _ = []

-- The Compiler tests using the standard library are horribly
-- slow at the moment (1min or more per test case).
stdlibTests :: Compiler -> IO TestTree
stdlibTests comp = do
  let testDir = "test" </> "Compiler" </> "with-stdlib"
  inps <- return [testDir </> "AllStdLib.agda"]
    -- put all tests in AllStdLib to avoid compiling the standard library
    -- multiple times

  let extraArgs :: [String]
      extraArgs = [ "-i" ++ testDir, "-i" ++ "std-lib" </> "src", "-istd-lib" ]

  let rtsOptions :: [String]
      rtsOptions = [ "+RTS", "-H2G", "-M1.5G", "-RTS" ]

  tests' <- forM inps $ \inp -> do
    opts <- readOptions inp
    return $
      agdaRunProgGoldenTest testDir comp (return $ extraArgs ++ rtsOptions) inp opts
  return $ testGroup "with-stdlib" $ catMaybes tests'


specialTests :: Compiler -> IO (Maybe TestTree)
specialTests _ = return Nothing

ghcArgsAsAgdaArgs :: GHCArgs -> AgdaArgs
ghcArgsAsAgdaArgs = map f
  where f = ("--ghc-flag=" ++)

agdaRunProgGoldenTest :: FilePath     -- ^ directory where to run the tests.
    -> Compiler
    -> IO AgdaArgs     -- ^ extra Agda arguments
    -> FilePath -- ^ relative path to agda input file.
    -> TestOptions
    -> Maybe TestTree
agdaRunProgGoldenTest dir comp extraArgs inp opts =
      agdaRunProgGoldenTest1 dir comp extraArgs inp opts (\compDir out err -> do
       -- TODO Remove
        if executeProg opts then do
          -- read input file, if it exists
          inp' <- maybe T.empty decodeUtf8 <$> readFileMaybe inpFile
          -- now run the new program
          let exec = getExecForComp comp compDir inpFile
          case comp of
            _ -> do
              (ret, out', err') <- PT.readProcessWithExitCode exec (runtimeOptions opts) inp'
              return $ ExecutedProg (ret, out <> out', err <> err')
        else
          return $ CompileSucceeded (ExitSuccess, out, err)
        )
  where inpFile = dropAgdaExtension inp <.> ".inp"

agdaRunProgGoldenTest1 :: FilePath     -- ^ directory where to run the tests.
    -> Compiler
    -> IO AgdaArgs     -- ^ extra Agda arguments
    -> FilePath -- ^ relative path to agda input file.
    -> TestOptions
    -> (FilePath -> T.Text -> T.Text -> IO ExecResult) -- continuation if compile succeeds, gets the compilation dir
    -> Maybe TestTree
agdaRunProgGoldenTest1 dir comp extraArgs inp opts cont
  | (Just cOpts) <- lookup comp (forCompilers opts) =
      Just $ goldenVsAction testName goldenFile (doRun cOpts) printExecResult
  | otherwise = Nothing
  where goldenFile = dropAgdaExtension inp <.> ".out"
        testName   = asTestName dir inp

        -- Andreas, 2017-04-14, issue #2317
        -- Create temporary files in system temp directory.
        -- This has the advantage that upon Ctrl-C no junk is left behind
        -- in the Agda directory.
        -- doRun cOpts = withTempDirectory dir testName (\compDir -> do
        doRun cOpts = withSystemTempDirectory testName (\compDir -> do
          -- get extra arguments
          extraArgs' <- extraArgs
          -- compile file
          let cArgs   = cleanUpOptions (extraAgdaArgs cOpts)
              defArgs = ["--ignore-interfaces" | notElem "--no-ignore-interfaces" (extraAgdaArgs cOpts)] ++
                        ["--no-libraries"] ++
                        ["--compile-dir", compDir, "-v0", "-vwarning:1"] ++ extraArgs' ++ cArgs ++ [inp]
          args <- (++ defArgs) <$> argsForComp comp
          res@(ret, out, err) <- readAgdaProcessWithExitCode args T.empty

          absDir <- canonicalizePath dir
          removePaths [absDir, compDir] <$> case ret of
            ExitSuccess -> cont compDir out err
            ExitFailure _ -> return $ CompileFailed res
          )

        argsForComp :: Compiler -> IO [String]
        argsForComp OCaml = return ["--mlf"]
        argsForComp _ = return []

        removePaths ps r = case r of
          CompileFailed    r -> CompileFailed    (removePaths' r)
          CompileSucceeded r -> CompileSucceeded (removePaths' r)
          ExecutedProg     r -> ExecutedProg     (removePaths' r)
          where
          removePaths' (c, out, err) = (c, rm out, rm err)

          rm = foldr (.) id $
               map (\p -> T.concat . T.splitOn (T.pack p)) ps

readOptions :: FilePath -- file name of the agda file
    -> IO TestOptions
readOptions inpFile =
  maybe defaultOptions (read . T.unpack . decodeUtf8) <$> readFileMaybe optFile
  where optFile = dropAgdaOrOtherExtension inpFile <.> ".options"

cleanUpOptions :: AgdaArgs -> AgdaArgs
cleanUpOptions = filter clean
  where
    clean :: String -> Bool
    clean "--no-ignore-interfaces"         = False
    clean o | isPrefixOf "--ghc-flag=-j" o = True
    clean _                                = True

-- gets the generated executable path
getExecForComp :: Compiler -> FilePath -> FilePath -> FilePath
getExecForComp _ compDir inpFile = compDir </> (takeFileName $ dropAgdaOrOtherExtension inpFile)

printExecResult :: ExecResult -> T.Text
printExecResult (CompileFailed r) = "COMPILE_FAILED\n\n" `T.append` printProcResult r
printExecResult (CompileSucceeded r) = "COMPILE_SUCCEEDED\n\n" `T.append` printProcResult r
printExecResult (ExecutedProg r) = "EXECUTED_PROGRAM\n\n" `T.append` printProcResult r
