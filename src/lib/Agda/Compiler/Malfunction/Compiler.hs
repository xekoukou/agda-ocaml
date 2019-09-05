{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{- |
Module      :  Agda.Compiler.Malfunction.Compiler
Maintainer  :  janmasrovira@gmail.com, hanghj@student.chalmers.se

This module includes functions that compile from <agda.readthedocs.io Agda> to
<https://github.com/stedolan/malfunction Malfunction>.
-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
module Agda.Compiler.Malfunction.Compiler
  (
  -- * Translation functions
    translateTerms
  , translateDef
  , compile
  , runTranslate
  -- * Data needed for compilation
  , Env(..)
  , ConRep(..)
  , Arity
  , Export
  -- * Others
  , qnameNameId
  , wildcardTerm
  , namedBinding
  , nameToIdent
  , mlfTagRange
  , compilePrim
  , mkCompilerEnv
  , module Agda.Compiler.Malfunction.AST
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




import           Prelude hiding ((<>))
import           Agda.Utils.Pretty
import           Agda.Syntax.Internal hiding (Term)
import           Agda.TypeChecking.Substitute
import           Agda.TypeChecking.Primitive (getBuiltinName)
import           Agda.TypeChecking.Monad.Builtin
import           Agda.Utils.Lens
import           Agda.TypeChecking.Warnings






-- TODO Review this code.
dependencyGraph :: [(QName , (ModuleName , TTerm))] -> [SCC (QName , (ModuleName , TTerm))]
dependencyGraph qs = stronglyConnComp [ ((qn, (mn , tt)), qnameNameId qn, edgesFrom tt)
                                    | (qn, (mn , tt)) <- qs ]
  where edgesFrom = Set.toList . qnamesIdsInTerm


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


-- Contains information about constructors that are to be inlined. Some constructors cannot be inlined.
data Env = Env
  { conMap :: Map NameId ConRep
  , level :: Int
  }
  deriving (Show)

-- | Data needed to represent a constructor
data ConRep =
    BlockRep
  { conTag    :: Int
  , conArity' :: Int
  , conInd'   :: Induction
  }
  | IntRep
    { conTag :: Int
    , conInd' :: Induction }
            deriving (Show)

type Arity = Int

runTranslate :: Reader Env a -> Env -> a
runTranslate = runReader

translateDefM :: MonadReader Env m => QName -> TTerm -> m Binding
translateDefM qnm t
  | isRecursive = do
      tt <- translateM t
      let iden = nameToIdent qnm
      return . Recursive . pure $ (iden, tt)
  | otherwise = do
      tt <- translateM t
      pure $ namedBinding qnm tt
  where
    -- TODO: I don't believe this is enough, consider the example
    -- where functions are mutually recursive.
    --     a = b
    --     b = a
    isRecursive = Set.member (qnameNameId qnm) (qnamesIdsInTerm t) -- TODO: is this enough?


mlfTagRange :: (Int, Int)
mlfTagRange = (0, 199)




qnameToConc :: QName -> String
qnameToConc qnm = concreteName qnm where
    toValid :: Char -> String
    toValid c
      | any (`inRange`c) [('0','9'), ('a', 'z'), ('A', 'Z')]
        || c == '_' = [c]
      | otherwise      = "{" ++ show (ord c) ++ "}"
    showNames = intercalate "." . map (concatMap toValid . show . nameConcrete)
    concreteName qn = showNames (mnameToList (qnameModule qn) ++ [qnameName qn])



-- | Returns all constructors grouped by data type.
getConstrNms :: [Definition] -> [[QName]]
getConstrNms = mapMaybe (getCons . theDef)
  where
    getCons :: Defn -> Maybe [QName]
    getCons c@Datatype{} = Just (dataCons c)
    -- The way I understand it a record is just like a data-type
    -- except it only has one constructor and that one constructor
    -- takes as many arguments as the number of fields in that
    -- record.
    getCons c@Record{}   = Just . pure . recCon $ c
    getCons _            = Nothing


getConstrInfo :: [[QName]] -> TCM [[(QName , (Arity , Induction))]]
getConstrInfo allcons
  | any ((>rangeSize mlfTagRange) . length) allcons = error "too many constructors"
  | otherwise = mapM (mapM (\q -> (q,) <$> infoQName q)) allcons


-- | If the qnames references a constructor the arity and induction property of that constructor is returned.
infoQName :: QName -> TCM (Int , Induction)
infoQName q = f . theDef <$> getConstInfo q
  where
    f def = case def of
      Constructor{} -> (conArity def , conInd def)
      _             -> __IMPOSSIBLE__





mkCompilerEnv' :: [[(QName, (Arity , Induction))]] -> Env
mkCompilerEnv' consByDtype = Env {
  conMap = conMap
  , level = 0
  }
  where
    singleDt :: Int -> Int -> [(QName , (Arity , Induction))] -> [(NameId , ConRep)]
    singleDt ci vi ((q , (0 , ind)) : ms) = (qnameNameId q , IntRep {conTag = ci , conInd' = ind}) : singleDt (ci + 1) vi ms
    singleDt ci vi ((q , (a , ind)) : ms) = (qnameNameId q , BlockRep {conTag = vi , conArity' = a , conInd' = ind}) : singleDt ci (vi + 1) ms
    singleDt _ _ [] = []
    
    conMap = Map.fromList (concatMap (singleDt 0 0) consByDtype)
--     conMap = Map.fromList [ (qnameNameId qn, ConRep {..} )
--                           | typeCons <- consByDtype
--                            , (length consByDtype <= rangeSize mlfTagRange)
--                              || error "too many constructors"
--                            , (_conTag, (qn, _conArity)) <- zip (range mlfTagRange) typeCons ]


mkCompilerEnv :: [Definition] -> TCM Env
mkCompilerEnv defs = do
  let cns = getConstrNms defs
  cinfo <- getConstrInfo cns
  pure $ mkCompilerEnv' cinfo


-- | Translate a single treeless term to a list of malfunction terms.
--
-- Note that this does not handle mutual dependencies correctly. For this you
-- would need @compile@.
translateDef :: Env -> QName -> TTerm -> Binding
translateDef env qn = (`runTranslate` env) . translateDefM qn

-- | Translates a list treeless terms to a list of malfunction terms.
--
-- Pluralized version of @translateDef@.
translateTerms :: Env -> [TTerm] -> [Term]
translateTerms env = (`runTranslate` env) . mapM translateM

translateM :: MonadReader Env m => TTerm -> m Term
translateM = translateTerm


translateTerm :: MonadReader Env m => TTerm -> m Term
translateTerm = \case
  TVar i            -> indexToVarTerm i
  TPrim tp          -> return $ translatePrim tp
  TDef name         -> pure $ translateName name
  TApp t0 args      -> translateApp t0 args
  tt@TLam{}         -> translateLam tt
  TLit lit          -> return $ translateLit lit
  TCon nm           -> translateCon nm
  TLet t0 t1        -> do
    t0' <- translateTerm t0
    (var, t1') <- introVar (translateTerm t1)
    return (Mlet [Named var t0'] t1')
  -- @deflt@ is the default value if all @alt@s fail.

-- TODO Handle the case where this is a lazy match if possible.
--     case (caseLazy cinfo) of
--       True -> pure $ error "caseLazy error."
--       False -> do

  TCase i _ deflt alts -> do
      t <- indexToVarTerm i
      d <- translateTerm deflt
      translateTCase t d alts
  TUnit             -> return Prim.unitT
  TSort             -> return Prim.unitT
  TErased           -> return Prim.unitT
                                    -- TODO: We can probably erase these , but we would have to change 
                                    -- the functions that use them , reduce their arity.
                                    -- For now, we simply pass the unit type.
  TError TUnreachable -> return wildcardTerm
  TCoerce{}         -> error "Malfunction.Compiler.translateTerm: TODO"

-- | We use this when we don't care about the translation.
wildcardTerm :: Term
wildcardTerm = Prim.errorT "__UNREACHABLE__"


indexToVarTerm :: MonadReader Env m => Int -> m Term
indexToVarTerm i = do
  ni <- asks level
  return (Mvar (ident (ni - i - 1)))



-- TODO Review this code.
translateTACon :: MonadReader Env m => Term -> [TAlt] -> m ([TAlt] , ([([Case] , Term)] , Induction))
translateTACon tcase (TACon con arity t : ts) = do
      usedFields <- snd <$> introVars arity
         (Set.map (\ix -> arity - ix - 1) . Set.filter (<arity) <$> usedVars t)
      (vars, t') <- introVars arity (translateTerm t)

      cnr <- askConRep con
      let (cs , ind) = case cnr of
                         BlockRep{conTag = tg , conInd' = ind'} -> (Tag tg , ind')
                         IntRep{conTag = tg , conInd' = ind'}   -> (CaseInt tg , ind')

      -- TODO: It is not clear how to deal with bindings in a pattern
      (rmalts , (rmcs , ind2)) <- translateTACon tcase ts
      
      let aind = allInd ind ind2
      
      let bt = bindFields vars usedFields tcase t' aind
      pure (rmalts , ((([cs], bt) : rmcs) , aind))      where
        allInd Inductive Inductive = Inductive
        allInd _ _ = CoInductive
translateTACon _ ts = pure (ts , ([] , Inductive))

translateTALit :: MonadReader Env m => Term -> TAlt -> m (Term , Term)
translateTALit tcase (TALit pat body) = do
      t <- translateTerm body
      let tgrd = litToCase tcase pat
      pure (tgrd , t)
translateTALit _ _ = __IMPOSSIBLE__

translateTAGuard :: MonadReader Env m => TAlt -> m (Term , Term)
translateTAGuard (TAGuard grd t) = do
       tgrd <- translateTerm grd
       tt  <- translateTerm t
       pure (tgrd , tt)
translateTAGuard _ = __IMPOSSIBLE__


translateLitOrGuard :: MonadReader Env m => Term -> [TAlt] -> m [(Term , Term)]
translateLitOrGuard tcase (c@(TALit _ _) : ts) = do
  r <- translateTALit tcase c
  rs <- translateLitOrGuard tcase ts
  pure $ r : rs
translateLitOrGuard tcase (c@(TAGuard _ _) : ts) = do
  r <- translateTAGuard c
  rs <- translateLitOrGuard tcase ts
  pure $ r : rs
translateLitOrGuard _ [] = pure []
translateLitOrGuard _ _ = __IMPOSSIBLE__

boolCases :: Term -> [(Term , Term)] -> Term
boolCases defaultt ((grd , body) : cs) = Mswitch grd [(trueCase , body) , (defaultCase , boolCases defaultt cs)]
boolCases defaultt [] = defaultt

-- tcase is (Var i)
-- default is the default case , in case all other fail.
translateTCase :: MonadReader Env m => Term -> Term -> [TAlt] -> m Term
translateTCase tcase defaultt tas = do
  (rmAlts , (cs , ind)) <-translateTACon tcase tas
  grdcs <- translateLitOrGuard tcase rmAlts
  case ind of
    Inductive -> pure $ Mswitch tcase (cs ++ [(defaultCase , boolCases defaultt grdcs)])
    CoInductive -> pure $ Mswitch (Mforce tcase) (cs ++ [(defaultCase , boolCases defaultt grdcs)])


defaultCase :: [Case]
defaultCase = [CaseAnyInt, Deftag]

bindFields :: [Ident] -> Set Int -> Term -> Term -> Induction -> Term
bindFields vars used termc body ind = case map bind varsRev of
  [] -> body
  binds -> Mlet binds body
  where
    varsRev = zip [0..] (reverse vars)
    bind (ix, iden)
      -- TODO: we bind all fields. The detection of used fields is bugged.
      | True || Set.member ix used =
        case ind of
          Inductive -> Named iden (Mfield ix termc)
          CoInductive -> Named iden (Mfield ix (Mforce termc))

      | otherwise = Named iden wildcardTerm

-- t here is (Var i)
litToCase :: Term -> Literal -> Term
litToCase t (LitNat _ i) = Mbiop Eq TBigint t (Mint (CBigint i))
litToCase t (LitChar _ c) = Mapply (Prim.primCode "primCharEqual") [t , (Mint $ CInt (fromEnum c))]
litToCase t (LitString _ s) = Mapply (Prim.primCode "string_equality") [t , Mstring s]
litToCase _ _ = error "Not Implemented"




-- The argument is the lambda itself together with its body.
translateLam :: MonadReader Env m => TTerm -> m Term
translateLam lam = do
  (is, t) <- translateLams lam
  return $ Mlambda is t
  where
    translateLams :: MonadReader Env m => TTerm -> m ([Ident], Term)
    translateLams (TLam body) = do
      (thisVar, (xs, t)) <- introVar (translateLams body)
      return (thisVar:xs, t)
    translateLams e = do
      e' <- translateTerm e
      return ([], e')



introVars :: MonadReader Env m => Int -> m a -> m ([Ident], a)
introVars k ma = do
  (names, env') <- nextIdxs k
  r <- local (const env') ma
  return (names, r)
  where
    nextIdxs :: MonadReader Env m => Int -> m ([Ident], Env)
    nextIdxs k' = do
      i0 <- asks level
      e <- ask
      return (map ident $ reverse [i0..i0 + k' - 1], e{level = level e + k'})

introVar :: MonadReader Env m => m a -> m (Ident, a)
introVar ma = first head <$> introVars 1 ma

-- This is also used to place the Mlazy in the correct place.
betareduction :: (Term , [Term]) -> Term
betareduction ((Mlambda ids t) , xs) = hp ids t xs
  where
    hp (id : ids) t (x : xs) = hp ids (replaceTr (Mvar id) x t) xs
    hp [] t (x : xs) = Mapply t (x : xs)
    hp (id : ids) t [] = Mlambda (id : ids) t
    hp [] t [] = t
betareduction (Mlazy (Mlambda ids t) , xs) = Mlazy $ hp ids t xs
  where
    hp (id : ids) t (x : xs) = hp ids (replaceTr (Mvar id) x t) xs
    hp [] t (x : xs) = Mapply t (x : xs)
    hp (id : ids) t [] = Mlambda (id : ids) t
    hp [] t [] = t
betareduction (t , xs) = Mapply t xs

translateApp :: MonadReader Env m => TTerm -> [TTerm] -> m Term
translateApp ft xst =
  do
    f <- translateTerm ft
    xs <- mapM translateTerm xst
    pure $ betareduction (f , xs)

ident :: Int -> Ident
ident i = Ident $ "v" ++ show i

translateLit :: Literal -> Term
translateLit l = case l of
  LitNat _ x -> Mint (CBigint x)
  LitString _ s -> Mstring s
  LitChar _ c -> Mint $ CInt (fromEnum c)
  _ -> Prim.errorT "unsupported literal type" 

translatePrim :: TPrim -> Term
translatePrim tp =
  case tp of
    PAdd -> intbinop TBigint Add
    PSub -> intbinop TBigint Sub
    PMul -> intbinop TBigint Mul
    PQuot -> intbinop TBigint Div
    PRem -> intbinop TBigint Mod
    PGeq -> intbinop TBigint Gte
    PLt -> intbinop TBigint Lt
    PEqI -> intbinop TBigint Eq
    PEqF -> wrong
    PEqS -> wrong
    PEqC -> wrong
    PEqQ -> wrong
    PIf -> wrong
    PSeq -> Mlambda ["a" , "b"] $ Mseq [ (Mvar "a") , (Mvar "b") ]
-- OCaml does not support unsigned Integers.
    PAdd64 -> notSupported
    PSub64 -> notSupported
    PMul64 -> notSupported
    PQuot64 -> notSupported
    PRem64 -> notSupported
    PLt64 -> notSupported
    PEq64 -> notSupported
    PITo64 -> notSupported
    P64ToI -> notSupported
  where
    intbinop typ op = Mlambda ["a" , "b"] $ Mbiop op typ (Mvar "a") (Mvar "b")
    
    -- TODO The RedBlack.agda test gave 3 args in pseq where the last one was unreachable.
    notSupported = Prim.errorT "Not supported by the OCaml backend."
    wrong = undefined




-- |
-- Set of indices of the variables that are referenced inside the term.
--
-- Example
-- λλ Env{level = 2} usedVars (λ(λ ((Var 3) (λ (Var 4)))) ) == {1}
usedVars :: MonadReader Env m => TTerm -> m (Set Int)
usedVars term = asks level >>= go mempty
   where
     go vars0 topnext = goterm vars0 term
       where
         goterms = foldM (\acvars tt -> goterm acvars tt)
         goterm vars t = do
           nextix <- asks level
           case t of
             (TVar v) -> return $ govar vars v nextix
             (TApp t0 args) -> goterms vars (t0:args)
             (TLam t0) -> snd <$> introVar (goterm vars t0)
             (TLet t1 t2) -> do
               vars1 <- goterm vars t1
               snd <$> introVar (goterm vars1 t2)
             (TCase v _ def alts) -> do
               vars1 <- goterm (govar vars v nextix) def
               foldM (\acvars alt -> goalt acvars alt) vars1 alts
             _ -> return vars
         govar vars v nextix
           | 0 <= v' && v' < topnext = Set.insert v' vars
           | otherwise = vars
           where v' = v + topnext - nextix
         goalt vars alt = case alt of
           TACon _ _ b -> goterm vars b
           TAGuard g b -> goterms vars [g, b]
           TALit{} -> return vars




translateCon :: MonadReader Env m => QName -> m Term
translateCon nm = do
      cnr <- askConRep nm
      case cnr of
        BlockRep{conTag = tag , conArity' = arity , conInd' = conInd} -> do
          let vs = take arity $ map (Ident . pure) ['a'..]
          case conInd of
            Inductive -> pure $ Mlambda vs (Mblock tag (map Mvar vs))
            -- The Mlazy is incorrectly placed here, but betareduction and "let elimination" will fix this.
            CoInductive -> pure $ Mlazy $ Mlambda vs (Mblock tag (map Mvar vs))
        IntRep{conTag = tag} -> pure $  Mint $ CInt tag




askConRep :: MonadReader Env f => QName -> f ConRep
askConRep q = fromMaybe err <$> lookupConRep q
  where
    err = __IMPOSSIBLE__

lookupConRep :: MonadReader Env f => QName -> f (Maybe ConRep)
lookupConRep ns = Map.lookup (qnameNameId ns) <$> asks conMap



translateName :: QName -> Term
translateName qn = Mvar (nameToIdent qn)

-- | Translate a Treeless name to a valid identifier in Malfunction
--
-- Not all names in agda are valid names in Treleess. Valid names in Agda are
-- given by [1]. Valid identifiers in Malfunction is subject to change:
--
-- "Atoms: sequences of ASCII letters, digits, or symbols (the exact set of
-- allowed symbols isn't quite nailed down yet)"[2]
--
-- [1. The Agda Wiki]: <http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual2.Identifiers>
-- [2. Malfunction Spec]: <https://github.com/stedolan/malfunction/blob/master/docs/spec.md>


nameToIdent :: QName -> Ident
nameToIdent qn = nameIdToIdent' (qnameNameId qn) (qnameToConc qn)

nameIdToIdent' :: NameId -> String -> Ident
nameIdToIdent' (NameId a b) msuffix = Ident ("agdaIdent" ++ hex a ++ "." ++ hex b ++ suffix)
  where
    suffix = ('.':) msuffix
    hex = (`showHex` "") . toInteger


-- | Translates a treeless identifier to a malfunction identifier.
qnameNameId :: QName -> NameId
qnameNameId = nameId . qnameName



translateBindingPair :: MonadReader Env m => QName -> TTerm -> m (Ident, Term)
translateBindingPair q t = do
  let iden = nameToIdent q
  (\t' -> (iden, t')) <$> translateTerm t



trueCase :: [Case]
trueCase = [CaseInt 1]



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

namedBinding :: QName -> Term -> Binding
namedBinding q t = (`Named`t) $ nameToIdent q




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
       -- TODO is this necessary? Probably yes.
      _ | Just OCDefn{} <- pragma, Just q == mflat ->
        genericError
          "\"COMPILE OCaml\" pragmas are not allowed for the FLAT builtin."


      _ | Just (OCDefn r oc) <- pragma -> setCurrentRange r $ do
        -- Check that the function isn't INLINE (since that will make this
        -- definition pointless).
        inline <- (^. funInline) . theDef <$> getConstInfo q
        when inline $ warning $ UselessInline q
        -- TODO At the moment we do not check that the type of the OCaml function corresponds to the
        -- type of the agda function or the postulate.
        let ident = nameToIdent q
            longIdent = topModNameToLIdent "ForeignCode" (toTopLevelModuleName mn) oc
        pure $ Just $ Right (ident , (Mglobal longIdent))
        

      -- TODO is this necessary?
      -- Compiling Inf
      _ | Just q == minf -> genericError "Inf is not supported at the moment."


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
      Primitive{} -> pure $ Just $ Left def
      Function{} -> pure $ Just $ Left def
      _ -> pure Nothing





-- The map is used to check if the definition has already been processed.
-- This is due to recursive definitions.
handleFunctionNoPragma :: Env -> Definition -> TCM (Maybe (Ident , Term))
handleFunctionNoPragma env (Defn{defName = q , theDef = d}) = 
  case d of
    Function{funDelayed = delayed} ->
       do
         case delayed of
-- TODO Handle the case where it is delayed. Delayed is the wrong primitive here. Fix this.
           Delayed -> error $ "Delayed is set to True for function name :" ++ prettyShow q
           NotDelayed -> do
              mt <- toTreeless EagerEvaluation q
              pure $ maybe Nothing (\t -> Just $ runTranslate (translateBindingPair q t) env) mt
    Primitive{primName = s} -> pure $ compilePrim q s
    _ -> pure $ error "At handleFunction : Case not expected."
        

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

handleFunction :: Env -> (ModuleName , Definition) -> TCM (Maybe (Ident , Term))
handleFunction env (mn , def) = do
  r <- handlePragma mn def
  case r of
    Nothing -> pure Nothing
    Just (Right bs) -> Just <$> wIOFunction def bs 
    Just (Left _) -> do
      b <- handleFunctionNoPragma env def 
      maybe (pure Nothing) (\x -> Just <$> wIOFunction def x) b


handleFunctions :: Env -> [(ModuleName , Definition)] -> TCM [Binding]
handleFunctions env allDefs = do
  let (others , fns) = splitPrim allDefs
  os <- mapM (handleFunction env) others
  let obs = map (\x -> Named (fst x) (snd x)) (catMaybes os)
  qts <- mapM (\(mn , x) -> do
                  let q = defName x
                  noC <- defNoCompilation <$> getConstInfo q
                  case noC of
                    True -> pure Nothing
                    False -> do
                      t <- toTreeless EagerEvaluation q
                      pure $ maybe Nothing (\rt -> Just (q , (mn , rt))) t) fns
  let recGrps = dependencyGraph (catMaybes qts)
  tmp <- mapM translateSCC recGrps
  pure $ obs ++ (catMaybes tmp)           where
    translateSCC scc = case scc of
      AcyclicSCC single -> do
        def <- getConstInfo (fst single)
        rs <- handleFunction env ((fst (snd single)) , def)
        pure $ maybe Nothing (\x -> Just $ Named (fst x) (snd x)) rs
      CyclicSCC grp -> do
        defs <- mapM (getConstInfo . fst) grp
        let mns = map (fst . snd) grp
        rs <- mapM (handleFunction env) (zip mns defs)
        case (catMaybes rs) of
          [] -> pure Nothing
          rss -> pure $ Just $ Recursive rss
     -- We handle primitives differently here because
     -- toTreeless fails on primitives.
    splitPrim :: [(ModuleName , Definition)] -> ([(ModuleName , Definition)] , [(ModuleName , Definition)])
    splitPrim = partitionEithers . map (\(mn , def) -> case (theDef def) of
                                        Function{} -> Right (mn , def)
                                        _        -> Left (mn , def) ) 
              



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
  let (dts , others) = split defs
  env <- mkCompilerEnv dts
  exs <- mapM handleExport (map snd others)
  bs <- handleFunctions env others
  pure (bs , catMaybes exs) where
    split :: [(ModuleName , Definition)] -> ([Definition] , [(ModuleName , Definition)])
    split xs = partitionEithers
               $ map (\(mn , x) -> case theDef x of
                       Datatype{} -> Left x
                       Record{} -> Left x
                       _ ->  Right (mn , x)  ) xs



