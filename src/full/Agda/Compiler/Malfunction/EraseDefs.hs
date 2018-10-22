{-# OPTIONS_GHC -Wall #-}
module Agda.Compiler.Malfunction.EraseDefs (eraseB , findUsedIdents) where

import Prelude hiding (id)
import Agda.Compiler.Malfunction.AST
import Agda.Compiler.Malfunction.Primitive
import Agda.Compiler.Common
import Data.List
import qualified Data.Map.Strict as M
import qualified Data.Generics.Uniplate.Data as Uniplate

findAllIdents :: [Binding] -> [(Ident , Term)]
findAllIdents (Named id t : xs) = (id , t) : findAllIdents xs
findAllIdents (Recursive ys : xs) = ys ++ findAllIdents xs
findAllIdents (_ : xs) = findAllIdents xs
findAllIdents [] = []


findMain :: [(Ident , Term)] -> Maybe (Ident , Term)
findMain ms = let fms = filter (\(Ident x , _t) -> "main" `isSuffixOf` x) ms
              in case fms of
                  [] -> Nothing
                  [x] -> Just x
                  (_ : _) -> error "Multiple functions with the name main exist."


findAllUsedBindings :: M.Map Ident Term -> Term -> M.Map Ident Term
findAllUsedBindings env0 t0 = snd $ foldr g (nEnv , newItems) nid
  where
  nid = concatMap f $ findUsedIdents t0
  newItems = M.fromList nid
  nEnv = M.difference env0 newItems
  f x = case M.lookup x env0 of
    Just a -> [(x , a)]
    _ -> []
  g (_ , t) (env , items) = (M.difference env ni , M.union ni items)
    where
    ni = findAllUsedBindings env t

-- The list is greater than the global lists because we have local identifiers.
findUsedIdents :: Term -> [Ident]
findUsedIdents = foldMap step . Uniplate.universe
  where
  step :: Term -> [Ident]
  step = \case
    Mvar i             -> pure i
    Mlambda is _       -> is
    Mapply{}           -> mempty
    Mlet{}             -> mempty
    Mseq{}             -> mempty
    Mint{}             -> mempty
    Mstring{}          -> mempty
    Mglobal{}          -> mempty
    Mswitch{}          -> mempty
    Muiop{}            -> mempty
    Mbiop{}            -> mempty
    Mconvert{}         -> mempty
    Mvecnew{}          -> mempty
    Mvecget{}          -> mempty
    Mvecset{}          -> mempty
    Mveclen{}          -> mempty
    Mblock{}           -> mempty
    Mfield{}           -> mempty



eraseB :: [Binding] -> (IsMain , [Binding])
eraseB bs = case findMain allIds of
  Just main -> (IsMain , f main)
  Nothing -> (NotMain , bs)
  where
  allIds = findAllIdents bs

  f :: (Ident, Term) -> [Binding]
  f main =
    (foldr g [] bs) ++ [Named (Ident "main") (Mapply (snd main) [unitT])]
    where
    env = M.delete (fst main) (M.fromList allIds)
    allUM = findAllUsedBindings env (snd main)

    g :: Binding -> [Binding] -> [Binding]
    g x osum = case x of
      Named id _t ->
        case M.lookup id allUM of
          Just _ -> x : osum
          _ -> osum
      Recursive ys ->
        case filter p ys of
          [] -> osum
          rs -> Recursive rs : osum
        where
          p (id , _) = case M.lookup id allUM of
            Just _ -> True
            _      -> False
      Unnamed{} -> error
          $  "Agda.Compiler.Malfunction.EraseDefs.f.g: "
          ++ "Non-exhaustive pattern match!"
