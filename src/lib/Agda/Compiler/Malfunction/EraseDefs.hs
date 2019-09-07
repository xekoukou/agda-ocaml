module Agda.Compiler.Malfunction.EraseDefs (eraseB , findUsedIdents) where

import Agda.Compiler.Malfunction.AST
import Agda.Compiler.Malfunction.Primitive
import Agda.Compiler.Common
import Data.List
import qualified Data.Map.Strict as M
import qualified Data.Generics.Uniplate.Data as Uniplate

findAllIdents :: [Binding] -> [(Ident , (String , Term))]
findAllIdents (Named id cn t : xs) = (id , (cn , t)) : findAllIdents xs
findAllIdents (Recursive ys : xs) = ys ++ findAllIdents xs
findAllIdents (_ : xs) = findAllIdents xs
findAllIdents [] = []


findMain :: [(Ident , (String , Term))] -> Maybe (Ident , (String , Term))
findMain ms = let fms = filter (\(_ , (x , _)) -> "main" `isSuffixOf` x) ms
              in case fms of
                  [] -> Nothing
                  [x] -> Just x
                  (_ : _) -> error "Multiple functions with the name main exist."


findAllUsedBindings :: M.Map Ident (String , Term) -> Term -> M.Map Ident (String , Term)
findAllUsedBindings env0 t0 = snd $ foldr g (nEnv , newItems) nid
  where
  nid' = concatMap f $ findUsedIdents t0
  newItems = M.intersection (M.fromList nid') env0
  nid = M.toList newItems
  nEnv = M.difference env0 newItems
  f x = case M.lookup x env0 of
    Just a -> [(x , a)]
    _ -> []
  g (_ , t) (env , items) = (M.difference env ni , M.union ni items)
    where
    ni = findAllUsedBindings env (snd t)

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
    Mblock{}           -> mempty
    Mfield{}           -> mempty
    Mlazy{}            -> mempty
    Mforce{}           -> mempty


initFAU :: (Ident, (String , Term)) -> M.Map Ident (String , Term) -> (M.Map Ident (String , Term) , M.Map Ident (String , Term))
initFAU (i , (_ , t)) allIds
                 = let env = M.delete i allIds
                       newItems = findAllUsedBindings env t
                   in (M.difference env newItems , newItems)


-- Second argument is the list of exports if we return a library.
-- If it is a library, we return only those used by the exorts
-- otherwise only those used by main.

eraseB :: [Binding] -> Maybe [Ident] -> (IsMain , [Binding])
eraseB _ (Just []) = (NotMain , [])
eraseB bs (Just exids) =
  let allIds = findAllIdents bs
      exs = foldr (\x y -> case (lookup x allIds) of
                             Just q -> (x , q) : y
                             nothing -> y ) [] exids
      ubs = foldr (\x (env , y) -> let (nenv , nitems) = initFAU x env
                                   in (nenv , M.union y nitems) ) (M.fromList allIds , M.empty) exs
  in (NotMain , foldr (orderB (M.union (snd $ ubs) (M.fromList exs))) [] bs)
eraseB bs Nothing =
  case findMain allIds of
    Just main ->
      let ubs = snd $ initFAU main (M.fromList allIds)
      in (IsMain , (foldr (orderB ubs) [] bs) ++ [Named (Ident "main") "MMain" (Mapply (Mglobal run) [Mapply (snd (snd main)) [unitT]])])
    -- We return nothing because we will throw an error.
    Nothing -> (NotMain , [])
  where
  run = Longident [(Ident "ForeignCode") , (Ident "main_run")]
  allIds = findAllIdents bs



orderB :: M.Map Ident (String , Term) -> Binding -> [Binding] -> [Binding]
orderB allUM x osum = case x of
  Named id cn _t ->
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
