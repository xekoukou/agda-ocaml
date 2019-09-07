{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{- |
Module      :  Agda.Compiler.Malfunction.Compiler
Maintainer  :  Apostolis Xekoukoulotakis

-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
module Agda.Compiler.Malfunction.Compiler
  (
  compile
  , qnameNameId
  ) where

import           Agda.Syntax.Common (NameId(..) , Delayed(..) , Induction(..))
import           Agda.Syntax.Literal
import           Agda.Syntax.Treeless

import           Agda.Utils.Impossible

import           Data.List.Extra (intercalate)
import           Control.Monad.Reader
import           Data.Ix (inRange, rangeSize)
import           Data.Map (Map)
import           Data.Either
import qualified Data.Map as Map
import           Data.Maybe (mapMaybe , fromMaybe , catMaybes)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Tuple.Extra (first)
import           Numeric (showHex)
import           Data.Char (ord)
import           Data.Graph

import           Agda.TypeChecking.Monad.Base
import           Agda.TypeChecking.Reduce
import           Agda.TypeChecking.Monad hiding (getVerbosity)
  
import           Agda.Compiler.ToTreeless


import           Agda.Compiler.Malfunction.AST
import qualified Agda.Compiler.Malfunction.Primitive as Prim
import           Agda.Compiler.Malfunction.Pragmas
import           Agda.Compiler.Malfunction.Optimize
import           Agda.Compiler.Malfunction.TreelessToAST




import           Prelude hiding ((<>))
import           Agda.Utils.Pretty
import           Agda.Syntax.Internal hiding (Term)
import           Agda.TypeChecking.Substitute
import           Agda.TypeChecking.Primitive (getBuiltinName)
import           Agda.TypeChecking.Monad.Builtin
import           Agda.Utils.Lens
import           Agda.TypeChecking.Warnings


-- Concrete names should not be used in the identity. This is
-- used to introduce comments in the .mlf file.
qnameToConc :: QName -> String
qnameToConc qnm = concreteName qnm where
    toValid :: Char -> String
    toValid c
      | any (`inRange`c) [('0','9'), ('a', 'z'), ('A', 'Z')]
        || c == '_' = [c]
      | otherwise      = "{" ++ show (ord c) ++ "}"
    showNames = intercalate "." . map (concatMap toValid . show . nameConcrete)
    concreteName qn = showNames (mnameToList (qnameModule qn) ++ [qnameName qn])







dependencyGraph :: [(QName , (ModuleName , TTerm))] -> [SCC (QName , (ModuleName , TTerm))]
dependencyGraph qs = stronglyConnComp [ ((qn, (mn , tt)), qnameNameId qn, edgesFrom tt)
                                    | (qn, (mn , tt)) <- qs ]
  where
    edgesFrom = Set.toList . qnamesIdsInTerm
    qnamesIdsInTerm :: TTerm -> Set NameId
    qnamesIdsInTerm t = go t mempty
      where
        insertId q = Set.insert (qnameNameId q)
        go :: TTerm -> Set NameId -> Set NameId
        go t qs = case t of
          TDef q -> insertId q qs
          TApp f args -> foldr go qs (f:args)
          TLam b -> go b qs
          TCon q -> insertId q qs
          TLet a b -> foldr go qs [a, b]
          TCase _ _ p alts -> foldr qnamesInAlt (go p qs) alts
          _  -> qs
          where
            qnamesInAlt a qs = case a of
              TACon q _ t -> insertId q (go t qs)
              TAGuard t b -> foldr go qs [t, b]
              TALit _ b -> go b qs
    


type Export = (Ident , String)





handlePragma :: ModuleName -> Definition -> TCM (Maybe (Either Definition (Ident , Term)))
handlePragma mn def@Defn{defName = q , defType = ty , theDef = d} = do
  reportSDoc "compile.ghc.definition" 10 $ pure $ vcat
    [ text "Compiling" <+> (pretty q <> text ":")
    , nest 2 $ text (show d)
    ]
  pragma <- getOCamlPragma q
  minf   <- getBuiltinName builtinInf
  mflat  <- getBuiltinName builtinFlat
  
  case d of
      _ | Just q == mflat -> typeError $ CompilationError "Flat is not supported."
      _ | Just q == minf ->  typeError $ CompilationError "Inf is not supported."

      _ | Just (OCDefn r oc) <- pragma -> setCurrentRange r $ do
        let ident = nameToIdent q
            longIdent = topModNameToLIdent "ForeignCode" (toTopLevelModuleName mn) oc
        pure $ Just $ Right (ident , (Mglobal longIdent))

      Axiom{} -> do
        
       -- We ignore Axioms on Sets.
       -- This backend has a single predefined representation of
       -- datatypes.
        let tl = isSort $ unEl $ theCore $ telView' ty
        case tl of
            Just _ ->  pure Nothing
            _    -> case pragma of
                       Nothing -> do
                         genericWarning
                           $ fwords $ "Warning : There are postulates that have not been defined : " ++ prettyShow q
                         pure Nothing
                       _ -> __IMPOSSIBLE__

      Datatype{} -> __IMPOSSIBLE__
      Record{} -> __IMPOSSIBLE__
      Primitive{} -> __IMPOSSIBLE__
      Function{} -> pure $ Just $ Left def
      AbstractDefn{} -> pure $ Just $ Left def
      _ -> pure Nothing





handleFunctionNoPragma :: Env -> Definition -> TCM (Maybe (Ident , Term))
handleFunctionNoPragma env (Defn{defName = q , theDef = d}) = 
  case d of
    Function{funDelayed = delayed} ->
       do
         case delayed of
           Delayed -> typeError $ InternalError $ "Delayed is set to True for function name :" ++ prettyShow q
           NotDelayed -> do
              mt <- toTreeless EagerEvaluation q
              pure $ maybe Nothing (\t -> Just $ runTranslate (translateBindingPair q t) env) mt
    AbstractDefn{} ->
      do
         mt <- toTreeless EagerEvaluation q
         pure $ maybe Nothing (\t -> Just $ runTranslate (translateBindingPair q t) env) mt
    _ -> __IMPOSSIBLE__
        

-- We add a world token to all IO function as long as they do not return a function.
-- To check that, we look at the type to find the number of arguments and then we check
-- at the number of lambdas that the Term has at the start.

wIOFunction :: Definition -> (Ident , Term) -> TCM (Ident , Term)
wIOFunction def self@(id , t) = do
  mio <- getBuiltin' builtinIO
  case mio of
    Nothing -> pure self
    Just (Def io _) -> do
      ty <- normalise (defType def)
      let tv = telView' ty
      let ln = length (telToList $ theTel $ tv)
      case (unEl $ theCore tv) of
        Def d _ | d == io ->   case t of
                    Mlambda ids tt -> case (ln == length ids) of
                      True -> pure (id , Mlambda (ids ++ ["world"]) (Mapply tt [Mvar "world"]))
                      False -> pure (id , Mlambda ids tt)
                    _ -> case ln of
                      0 -> pure (id , Mlambda ["world"] (Mapply t [Mvar "world"]))
                      _ -> pure (id , t)
        _ -> pure self
    _ -> __IMPOSSIBLE__

handleFunction :: Env -> (ModuleName , Definition) -> TCM (Maybe (Ident , (String , Term)))
handleFunction env (mn , def@Defn{defName = q}) = do
  r <- handlePragma mn def
  case r of
    Nothing -> pure Nothing
    Just (Right bs) -> Just <$> addCn <$> wIOFunction def bs 
    Just (Left _) -> do
      b <- handleFunctionNoPragma env def 
      maybe (pure Nothing) (\x -> Just <$> addCn <$> wIOFunction def x) b
  where
    addCn = (\(i , t) -> (i , (qnameToConc q , t)))


handlePrimitives :: Env -> [(ModuleName , Definition)] -> TCM ([(ModuleName , Definition)] , [Binding])
handlePrimitives env [] = pure ([] , [])
handlePrimitives env ((mn , def@Defn{defName = q}) : xs) = do
    (odef , obs) <- handlePrimitives env xs
    case (theDef def) of
      Primitive{primName = s} -> maybe (pure (odef , obs)) (\r -> pure $ (odef , Named (fst r) (qnameToConc q) (snd r) : obs)) (compilePrim q s)
      _ -> pure ((mn , def) : odef , obs)
  where
    -- | Translates a primitive to a malfunction binding. Returns `Nothing` if the primitive is unmapped.
    compilePrim
      :: QName -- ^ The qname of the primitive
      -> String -- ^ The name of the primitive
      -> Maybe (Ident , Term)
    compilePrim q s = case x of
                        Just y -> Just (nameToIdent q , y)
                        Nothing -> Nothing
      where
        x = Map.lookup s Prim.primitives
  

handleAxioms :: Env -> [(ModuleName , Definition)] -> TCM ([(ModuleName , Definition)] , [Binding])
handleAxioms env [] = pure ([] , [])
handleAxioms env ((mn , def@Defn{defName = q}) : xs) = do
    (odef , obs) <- handleAxioms env xs
    case (theDef def) of
      Axiom -> do
                  r <- handlePragma mn def
                  case r of
                    Nothing              -> pure (odef , obs)
                    Just (Left _)        -> pure (odef , obs)
                    Just (Right (i , t)) -> pure $ (odef , Named i (qnameToConc q) t : obs)
      _ -> pure ((mn , def) : odef , obs)


handleFunctions :: Env -> [(ModuleName , Definition)] -> TCM [Binding]
handleFunctions env allDefs = do
  (odefs , pbs) <- handlePrimitives env allDefs
  (odefs , abs) <- handleAxioms env odefs
  qts <- mapM (\(mn , x) -> do
                  let q = defName x
                  t <- toTreeless EagerEvaluation q
                  pure $ maybe Nothing (\rt -> Just (q , (mn , rt))) t) (onlyFun odefs)
  let recGrps = dependencyGraph (catMaybes qts)
  tmp <- mapM translateSCC recGrps
  pure $ pbs ++ abs ++ (catMaybes tmp)           where
    translateSCC scc = case scc of
      AcyclicSCC single -> do
        def <- getConstInfo (fst single)
        rs <- handleFunction env ((fst (snd single)) , def)
        pure $ maybe Nothing (\x -> Just $ Named (fst x) (fst (snd x)) (snd (snd x))) rs
      CyclicSCC grp -> do
        defs <- mapM (getConstInfo . fst) grp
        let mns = map (fst . snd) grp
        rs <- mapM (handleFunction env) (zip mns defs)
        case (catMaybes rs) of
          [] -> pure Nothing
          rss -> pure $ Just $ Recursive rss
          
    onlyFun :: [(ModuleName , Definition)] -> [(ModuleName , Definition)]
    onlyFun = filter (\(mn , def) -> case (theDef def) of
                                         Function{}     -> True
                                         AbstractDefn{} -> True
                                         _              -> False) 
      
              



handleExport :: Definition -> TCM (Maybe Export)
handleExport Defn{defName = q} = do
  p <- getOCamlPragma q
  pure $ maybe Nothing (\x -> case x of
                           (OCExport _ s) -> Just (nameToIdent q , s)
                           _ -> Nothing) p


compile
  :: [(ModuleName , Definition)]
  -> TCM ([Binding] , [Export])
compile defs = do
  rdefs <- removeNoComp defs
  let (dts , others) = dataOrOther rdefs
  env <- constructEnv dts
  exs <- mapM handleExport (map snd others)
  bs <- handleFunctions env others
  pure (bs , catMaybes exs) where
    dataOrOther :: [(ModuleName , Definition)] -> ([Definition] , [(ModuleName , Definition)])
    dataOrOther xs = partitionEithers
               $ map (\(mn , x) -> case theDef x of
                       Datatype{} -> Left x
                       Record{} -> Left x
                       _ ->  Right (mn , x)  ) xs
    removeNoComp = filterM (\(_ , x) -> do
                    let q = defName x
                    noC <- defNoCompilation <$> getConstInfo q
                    return (not noC))



