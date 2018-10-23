{-# OPTIONS_GHC -Wall #-}
module Agda.Compiler.Malfunction.EraseDefs (eraseB , findUsedIdents) where

import Prelude hiding (id)
import Agda.Compiler.Malfunction.AST
import Agda.Compiler.Malfunction.Primitive
import Agda.Compiler.Common
import Data.List
import Data.Maybe
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



initFAU :: (Ident, Term) -> [(Ident , Term)] -> M.Map Ident Term
initFAU b allIds = let env = M.delete (fst b) (M.fromList allIds)
                   in findAllUsedBindings env (snd b)


-- Second argument is the list of exports if we return a library.
-- If it is a library, we return only those used by the exorts
-- otherwise only those used by main.

eraseB :: [Binding] -> Maybe [Ident] -> (IsMain , [Binding])
eraseB bs (Just []) = (NotMain , [])
eraseB bs (Just exids) =
  let allIds = findAllIdents bs
      exs = foldr (\x y -> y ++ maybe [] (\t -> [(x , t)]) (lookup x allIds)) [] exids
      ubs = foldr (\x y -> M.union y (initFAU x allIds)) M.empty exs
  in (NotMain , foldr (orderB (M.union ubs (M.fromList exs))) [] bs)
eraseB bs Nothing =
  case findMain allIds of
    Just main ->
      let ubs = initFAU main allIds
      in (IsMain , (foldr (orderB ubs) [] bs) ++ [Named (Ident "main") (Mapply (snd main) [unitT])])
    -- We return nothing because we will throw an error.
    Nothing -> (NotMain , [])
  where
  allIds = findAllIdents bs



orderB :: M.Map Ident Term -> Binding -> [Binding] -> [Binding]
orderB allUM x osum = case x of
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
