{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards, OverloadedStrings #-}
{- |
Module      :  Agda.Compiler.Malfunction.Compiler
Maintainer  :  janmasrovira@gmail.com, hanghj@student.chalmers.se

This module includes functions that compile from <agda.readthedocs.io Agda> to
<https://github.com/stedolan/malfunction Malfunction>.
-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wall -Wno-unused-top-binds #-}
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
  -- * Others
  , qnameNameId
  , errorT
  , boolT
  , wildcardTerm
  , namedBinding
  , nameToIdent
  , mlfTagRange
  -- * Primitives
  , compilePrim
  , mkCompilerEnv
  -- * Malfunction AST
  , module Agda.Compiler.Malfunction.AST
  ) where

import           Agda.Syntax.Common (NameId(..) , Delayed(..))
import           Agda.Syntax.Literal
import           Agda.Syntax.Treeless

import           Control.Monad.Extra (ifM)
import           Data.List.Extra (intercalate)
import           Control.Monad.Reader
import           Data.Ix (inRange, rangeSize)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (mapMaybe , fromMaybe , maybeToList , catMaybes)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Tuple.Extra (first)
import           Numeric (showHex)
import           Data.Char (ord)
import           GHC.Exts (IsList(..))

import           Agda.TypeChecking.Monad.Base
import           Agda.TypeChecking.Monad
import           Agda.TypeChecking.Positivity.Occurrence
  
import           Agda.Compiler.ToTreeless


import           Agda.Compiler.Malfunction.AST
import qualified Agda.Compiler.Malfunction.Primitive as Primitive


--TODO Remove
import Debug.Trace

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
  }
  | IntRep
    { conTag :: Int }
            deriving (Show)

type Translate a = Reader Env a
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


getConstrInfo :: [[QName]] -> TCM [[(QName , Arity)]]
getConstrInfo allcons
  | any ((>rangeSize mlfTagRange) . length) allcons = error "too many constructors"
  | otherwise = withArity allcons


-- | Creates a mapping for all the constructors in the array. The constructors
-- should reference the same data-type.
withArity :: [[QName]] -> TCM [[(QName, Int)]]
withArity = mapM (mapM (\q -> (q,) <$> arityQName q))

-- | If the qnames references a constructor the arity of that constructor is returned.
arityQName :: QName -> TCM Int
arityQName q = f . theDef <$> getConstInfo q
  where
    f def = case def of
      Constructor{} -> conArity def
      _             -> error "Not a constructor :("



mkCompilerEnv' :: [[(QName, Arity)]] -> Env
mkCompilerEnv' consByDtype = Env {
  conMap = conMap
  , level = 0
  }
  where
    singleDt :: Int -> Int -> [(QName , Arity)] -> [(NameId , ConRep)]
    singleDt ci vi ((q , 0) : ms) = (qnameNameId q , IntRep {conTag = ci}) : singleDt (ci + 1) vi ms
    singleDt ci vi ((q , a) : ms) = (qnameNameId q , BlockRep {conTag = vi , conArity' = a}) : singleDt ci (vi + 1) ms
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
  TCase i cinfo deflt alts -> do
    case (caseLazy cinfo) of
      True -> error "caseLazy error."
      False -> do
        t <- indexToVarTerm i
        alts' <- alternatives t
        return $ Mswitch t alts'
    where
      alternatives t = do
          d <- translateTerm deflt
          translateAltsChain t d alts
  TUnit             -> return Primitive.unitT
  TSort             -> return Primitive.unitT
  TErased           -> return Primitive.unitT
                                    -- TODO: We can probably erase these , but we would have to change 
                                    -- the functions that use them , reduce their arity.
                                    -- For now, we simply pass the unit type.
  TError TUnreachable -> return wildcardTerm
  TCoerce{}         -> error "Malfunction.Compiler.translateTerm: TODO"

-- | We use this when we don't care about the translation.
wildcardTerm :: Term
wildcardTerm = errorT "__UNREACHABLE__"


indexToVarTerm :: MonadReader Env m => Int -> m Term
indexToVarTerm i = do
  ni <- asks level
  return (Mvar (ident (ni - i - 1)))


-- TODO Review this code.
translateAltsChain :: MonadReader Env m => Term -> Term -> [TAlt] -> m [([Case], Term)]
translateAltsChain _ defaultt []
  = pure [(defaultCase, defaultt)]
translateAltsChain tcase defaultt (ta:tas) =
  case ta of
    TALit pat body -> do
      b <- translateTerm body
      let c = litToCase pat
      (([c], b):) <$> go
    TACon con arity t -> do
      usedFields <- snd <$> introVars arity
         (Set.map (\ix -> arity - ix - 1) . Set.filter (<arity) <$> usedVars t)
      (vars, t') <- introVars arity (translateTerm t)
      let bt = bindFields vars usedFields tcase t'
      -- TODO: It is not clear how to deal with bindings in a pattern
      
      cnr <- askConRep con
      let cs = case cnr of
                 BlockRep{conTag = tg} -> Tag tg
                 IntRep{conTag = tg} -> CaseInt tg
      (([cs], bt):) <$> go
    TAGuard grd t -> do
      tgrd <- translateTerm grd
      t' <- translateTerm t
      tailAlts <- go
      return [(defaultCase,
                Mswitch tgrd
                [(trueCase, t')
                , (defaultCase, Mswitch tcase tailAlts)])]
  where
    go = translateAltsChain tcase defaultt tas

defaultCase :: [Case]
defaultCase = [CaseAnyInt, Deftag]

bindFields :: [Ident] -> Set Int -> Term -> Term -> Term
bindFields vars used termc body = case map bind varsRev of
  [] -> body
  binds -> Mlet binds body
  where
    varsRev = zip [0..] (reverse vars)
    bind (ix, iden)
      -- TODO: we bind all fields. The detection of used fields is bugged.
      | True || Set.member ix used = Named iden (Mfield ix termc)
      | otherwise = Named iden wildcardTerm

litToCase :: Literal -> Case
litToCase l = case l of
  LitNat _ i -> CaseInt . fromInteger $ i
  _          -> error "Unimplemented"




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



translateApp :: MonadReader Env m => TTerm -> [TTerm] -> m Term
translateApp ft xst =
  do
    f <- translateTerm ft
    xs <- mapM translateTerm xst
    pure $ Mapply f xs

ident :: Int -> Ident
ident i = Ident $ "v" ++ show i

translateLit :: Literal -> Term
translateLit l = case l of
  LitNat _ x -> Mint (CBigint x)
  LitString _ s -> Mstring s
  -- TODO Check that this is correct. According to the OCaml spec,
  -- Chars are represented as Ints.
  LitChar _ c -> Mint . CInt . fromEnum $ c
  _ -> error "unsupported literal type"

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
    notSupported = error "Not supported by the OCaml backend."
    wrong = undefined






isConstructor :: MonadReader Env m => QName -> m Bool
isConstructor nm = (qnameNameId nm `Map.member`) <$> askConMap

askConMap :: MonadReader Env m => m (Map NameId ConRep)
askConMap = asks conMap

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
        BlockRep{conTag = tag , conArity' = arity} -> do
          let vs = take arity $ map (Ident . pure) ['a'..]
          pure $ Mlambda vs (Mblock tag (map Mvar vs))
        IntRep{conTag = tag} -> pure $  Mint $ CInt tag




askConRep :: MonadReader Env f => QName -> f ConRep
askConRep q = fromMaybe err <$> lookupConRep q
  where
    err = error $ "Could not find constructor with qname: " ++ show q

lookupConRep :: MonadReader Env f => QName -> f (Maybe ConRep)
lookupConRep ns = Map.lookup (qnameNameId ns) <$> asks conMap



translateName :: QName -> Term
translateName qn = Mvar $ nameToIdent qn

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


translateMutualGroup :: MonadReader Env m => [(QName, TTerm)] -> m Binding
translateMutualGroup bs = Recursive <$> mapM (uncurry translateBindingPair) bs

translateBinding :: MonadReader Env m => QName -> TTerm -> m Binding
translateBinding q t = uncurry Named <$> translateBindingPair q t

translateBindingPair :: MonadReader Env m => QName -> TTerm -> m (Ident, Term)
translateBindingPair q t = do
  let iden = nameToIdent q
  (\t' -> (iden, t')) <$> translateTerm t




qnamesIdsInTerm :: TTerm -> Set NameId
qnamesIdsInTerm term = go term mempty
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
        qnamesInAlt a qs' = case a of
          TACon q _ t' -> insertId q (go t' qs')
          TAGuard t' b -> foldr go qs' [t', b]
          TALit _ b -> go b qs'

-- | Defines a run-time error in Malfunction - equivalent to @error@ in Haskell.
errorT :: String -> Term
errorT err = Mapply (Mglobal (fromList ["Pervasives", "failwith"])) [Mstring err]

-- | Encodes a boolean value as a numerical Malfunction value.
boolT :: Bool -> Term
boolT b = Mint (CInt $ boolToInt b)

boolToInt :: Bool -> Int
boolToInt b = if b then 1 else 0

trueCase :: [Case]
trueCase = [CaseInt 1]

-- -- TODO: Stub implementation!
-- -- Translating axioms seem to be problematic. For the other compiler they are
-- -- defined in Agda.TypeChecking.Monad.Base. It is a field of
-- -- `CompiledRepresentation`. We do not have this luxury. So what do we do?
-- --
-- -- | Translates an axiom to a malfunction binding. Returns `Nothing` if the axiom is unmapped.
-- compileAxiom ::
--   QName                 -- The name of the axiom
--   -> Maybe Binding      -- The resulting binding
-- compileAxiom q = do
--                    case x of
--                      Just z -> Just $ namedBinding q z
--                      Nothing -> Nothing
--   where
--     x = Map.lookup (show q') Primitive.axioms
--     q' = last . qnameToList $ q

-- | Translates a primitive to a malfunction binding. Returns `Nothing` if the primitive is unmapped.
compilePrim
  :: QName -- ^ The qname of the primitive
  -> String -- ^ The name of the primitive
  -> Maybe Binding
compilePrim q s = case x of
                    Just y -> Just $ namedBinding q y
                    Nothing -> Nothing
  where
    x = Map.lookup s Primitive.primitives

namedBinding :: QName -> Term -> Binding
namedBinding q t = (`Named`t) $ nameToIdent q


allUnused :: [Occurrence] -> Bool
allUnused [] = True
allUnused (Unused : ms) = allUnused ms
allUnused (_ : _) = False


-- The map is used to check if the definition has already been processed.
-- This is due to recursive definitions.
handleFunction :: Env -> Definition -> Map QName Definition -> TCM (Map QName Definition , Maybe Binding)
handleFunction env def@(Defn{defName = q , defArgOccurrences = ocs , defNoCompilation = noC , theDef = d}) rmap = 
  case Map.lookup q rmap of
    Nothing -> pure (rmap , Nothing)
    Just _ -> case d of
      Function{funMutual = mrec , funDelayed = delayed} ->
       do
         case delayed of
-- TODO Handle the case where it is delayed.
           Delayed -> error $ "Delayed is set to True for function name :" ++ prettyShow q
           NotDelayed -> pure ()
      -- TODO Clean this if Agda's behavior changes.
         case noC || allUnused ocs of
           True -> pure ( Map.delete q rmap , Nothing)
           _ ->
             case mrec of
              Nothing -> error $ "the positivity checher has not determined mutual recursion yet : " ++ prettyShow def ++ "Should I compile?" ++ prettyShow noC
              Just [] ->  do
                mt <- toTreeless q
                pure ( Map.delete q rmap , maybe Nothing (\t -> Just $ runTranslate (translateBinding q t) env) mt)
              Just mq -> do
                mts <- mapM (\x -> do
                                     y <- toTreeless x
                                     case y of
                                       Just t -> pure $ Just (x , t)
                                       Nothing -> pure Nothing ) mq
                
                pure ( foldr Map.delete rmap mq , Just $ runTranslate (translateMutualGroup (catMaybes mts)) env)
      Primitive{primName = s} -> pure (Map.delete q rmap , compilePrim q s)
      _ -> pure $ error "At handleFunction : Case not expected."
        



handleFunctions :: Env -> [Definition] -> Map QName Definition -> TCM [Binding]
handleFunctions env (d : ds) mp = do
  (nmp , b) <- handleFunction env d mp
  (maybeToList b ++) <$> handleFunctions env ds nmp
handleFunctions _ [] _ = pure []
              



compile
  :: Env -> [Definition]
  -> TCM [Binding]
compile env defs = handleFunctions env defs (Map.fromList $ map (\x -> (defName x , x)) defs)



