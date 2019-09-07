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


module Agda.Compiler.Malfunction.TreelessToAST
  (
    Env ,
    constructEnv ,
    nameToIdent ,
    qnameNameId ,
    runTranslate ,
    translateBindingPair
    
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


constructEnv :: [Definition] -> TCM Env
constructEnv defs = do
  let cns = getConstrNms defs
  cinfo <- getConstrInfo cns
  pure $ constructEnv' cinfo where
    
-- | Returns all constructors grouped by data type.
  getConstrNms :: [Definition] -> [[QName]]
  getConstrNms = map (getCons . theDef)
    where
      getCons :: Defn -> [QName]
      getCons c@Datatype{} = dataCons c
      getCons c@Record{}   = pure . recCon $ c
      getCons _            = __IMPOSSIBLE__

  maxTagRange :: (Int, Int)
  maxTagRange = (0, 199)

  getConstrInfo :: [[QName]] -> TCM [[(QName , (Arity , Induction))]]
  getConstrInfo allcons
    | any ((>rangeSize maxTagRange) . length) allcons = typeError $ CompilationError "too many constructors"
    | otherwise = mapM (mapM (\q -> (q,) <$> infoQName q)) allcons where
  
    -- | If the qnames references a constructor the arity and induction property of that constructor is returned.
    infoQName :: QName -> TCM (Int , Induction)
    infoQName q = f . theDef <$> getConstInfo q
      where
        f def = case def of
          Constructor{} -> (conArity def , conInd def)
          _             -> __IMPOSSIBLE__

  constructEnv' :: [[(QName, (Arity , Induction))]] -> Env
  constructEnv' consByDtype = Env {
    conMap = conMap
    , level = 0
    }
    where
      -- We apply the same structure that exists internally for OCaml algebraic data types.
      singleDt :: Int -> Int -> [(QName , (Arity , Induction))] -> [(NameId , ConRep)]
      singleDt ci vi ((q , (0 , ind)) : ms) = (qnameNameId q , IntRep {conTag = ci , conInd' = ind}) : singleDt (ci + 1) vi ms
      singleDt ci vi ((q , (a , ind)) : ms) = (qnameNameId q , BlockRep {conTag = vi , conArity' = a , conInd' = ind}) : singleDt ci (vi + 1) ms
      singleDt _ _ [] = []
      
      conMap = Map.fromList (concatMap (singleDt 0 0) consByDtype)
  





  


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
    (Ident var, t1') <- introVar (translateTerm t1)
    return (Mlet [Named (Ident var) var t0'] t1')
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
  TError TUnreachable -> return (wildcardTerm "__UNREACHABLE__")
  TCoerce{}         -> error "Malfunction.Compiler.translateTerm: TODO"

-- | We use this when we don't care about the translation.
wildcardTerm :: String -> Term
wildcardTerm s = Prim.errorT s


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
                         BlockRep{conTag = tg , conInd' = ind'} -> (CaseTag tg , ind')
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
defaultCase = [CaseAnyInt, CaseAnyTag]

bindFields :: [Ident] -> Set Int -> Term -> Term -> Induction -> Term
bindFields vars used termc body ind = case map bind varsRev of
  [] -> body
  binds -> Mlet binds body
  where
    varsRev = zip [0..] (reverse vars)
    bind (ix, Ident iden)
      -- TODO: we bind all fields. The detection of used fields is bugged.
      | True || Set.member ix used =
        case ind of
          Inductive -> Named (Ident iden) iden (Mfield ix termc)
          CoInductive -> Named (Ident iden) iden (Mfield ix (Mforce termc))

      | otherwise = Named (Ident iden) iden (wildcardTerm iden)

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


nameToIdent :: QName -> Ident
nameToIdent qn = nameIdToIdent' (qnameNameId qn)
  where
    nameIdToIdent' :: NameId -> Ident
    nameIdToIdent' (NameId a b) = Ident ("agdaIdent" ++ hex a ++ "." ++ hex b)
      where
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

