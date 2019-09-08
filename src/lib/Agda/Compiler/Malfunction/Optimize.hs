{-# OPTIONS_GHC -Wall -Wno-name-shadowing -Wno-unused-matches#-}
module Agda.Compiler.Malfunction.Optimize (optimizeLetsB , replaceTr) where

import Agda.Compiler.Malfunction.AST
import Agda.Compiler.Malfunction.EraseDefs
import Data.List
import Data.Either
import qualified Data.Map.Strict as M

import Agda.Utils.Impossible
import Control.Monad.State


caseEq :: Term -> Term -> Term -> Term -> Term
caseEq rt ar t ot = case rt == t of
                     True -> ar
                     False -> ot


-- Respects shadowing, if a let statement or lambda has bound a specific variable, it does not
-- replace the term, thus it only replaces on the free variables.

replaceTr :: Term -> Term -> Term -> Term
replaceTr rt ar self@(Mvar i) = caseEq rt ar self self
replaceTr rt ar self@(Mlambda a t) = caseEq rt ar self $ case (allFalse (map ((rt ==) . Mvar) a)) of
    False  -> Mlambda a t
    True   -> Mlambda a (replaceTr rt ar t)
  where
    allFalse :: [Bool] -> Bool
    allFalse (False : xs) = allFalse xs
    allFalse (True : xs) = False
    allFalse _ = True
replaceTr rt ar self@(Mapply a bs) = caseEq rt ar self $ let (na : nbs) = map (replaceTr rt ar) (a : bs)
                                                         in Mapply na nbs 
replaceTr rt ar self@(Mlet bs t) =  caseEq rt ar self $ let e = map check bs
                                    in hf2 (hf (zip e bs)) (allFalse e)   where
  rpl :: Binding -> Binding
  rpl (Named x cn t) = Named x cn $ replaceTr rt ar t
  rpl (Recursive rs) = error "Let bindings cannot be recursive."

  check :: Binding -> Bool
  check (Named x _ _) = rt == Mvar x
  check (Recursive rs) = error "Let bindings cannot be recursive."

  allFalse :: [Bool] -> Bool
  allFalse (False : xs) = allFalse xs
  allFalse (True : xs) = False
  allFalse _ = True

  hf :: [(Bool , Binding)] -> [Binding]
  hf ((False , b) : bs) = rpl b : hf bs
  hf ((True , b) : bs) = b : hf bs
  hf [] = []
  hf _ = __IMPOSSIBLE__

  hf2 :: [Binding] -> Bool -> Term
  hf2 [] _     = replaceTr rt ar t
  hf2 bs True  = Mlet bs (replaceTr rt ar t)
  hf2 bs False = Mlet bs t

  
replaceTr rt ar self@(Mswitch ta tb) =  caseEq rt ar self $
                                          let nta = replaceTr rt ar ta
                                              ntb = map (replaceTr rt ar . snd) tb
                                          in Mswitch nta (zipWith (\(c , _) nb -> (c , nb)) tb ntb)
replaceTr rt ar self@(Muiop x y t) =  caseEq rt ar self $ let nt = replaceTr rt ar t
                                                          in Muiop x y nt
replaceTr rt ar self@(Mbiop x y ta tb ) =  caseEq rt ar self $
                                               let nta = replaceTr rt ar ta
                                                   ntb = replaceTr rt ar tb
                                               in Mbiop x y nta ntb
replaceTr rt ar self@(Mconvert x y t) =  caseEq rt ar self $
                                           let nt = replaceTr rt ar t
                                           in Mconvert x y nt
replaceTr rt ar self@(Mblock x bs) =  caseEq rt ar self $
                                        let nbs = map (replaceTr rt ar) bs
                                        in Mblock x nbs
replaceTr rt ar self@(Mfield x t) =  caseEq rt ar self $
                                       let nt = replaceTr rt ar t
                                       in Mfield x nt
replaceTr rt ar self@(Mseq ts) = caseEq rt ar self $
                                   let nts = map (replaceTr rt ar) ts
                                   in Mseq nts
replaceTr rt ar self = caseEq rt ar self self



-----------------------------------------------------------


--- We remove let statements . According to a treeless comment https://github.com/agda/agda/blob/master/src/full/Agda/Syntax/Treeless.hs#L44 , this is perfectly reasonable.

-- This is also important for Coinduction because the coinductive expression is pushed inside the constructor.
removeLets :: Term -> Term
removeLets self@(Mvar i) = self
removeLets (Mlambda a t) = let rm = removeLets t
                           in Mlambda a rm
removeLets (Mapply a bs) = let (na : nbs) = map removeLets (a : bs)
                           in Mapply na nbs 
removeLets (Mlet bs t) =  let mt = replaceTrL (map rpl bs) t
                              nt = removeLets mt
                          in nt where
  rpl :: Binding -> (Term , Term)
  rpl (Named x _ t) = (Mvar x , t)
  rpl (Recursive rs) = error "Let bindings cannot be recursive."

  replaceTrL :: [(Term , Term)] -> Term -> Term
  replaceTrL ((x , nx) : ms) t = let (nt : rnms) = map (replaceTr x nx) (t : map snd ms)
                                 in replaceTrL (zip (map fst ms) rnms) nt
  replaceTrL [] t = t
  
removeLets (Mswitch ta tb) = let nta = removeLets ta
                                 ntb = map (removeLets . snd) tb
                             in Mswitch nta (zipWith (\(c , _) nb -> (c , nb)) tb ntb)
removeLets (Muiop x y t) = let nt = removeLets t
                           in Muiop x y nt
removeLets (Mbiop x y ta tb ) = let nta = removeLets ta
                                    ntb = removeLets tb
                                in Mbiop x y nta ntb
removeLets (Mconvert x y t) = let nt = removeLets t
                              in Mconvert x y nt
removeLets (Mblock x bs) = let nbs = map removeLets bs
                           in Mblock x nbs
removeLets (Mfield x t) = let nt = removeLets t
                          in Mfield x nt
removeLets (Mlazy t) =  let nt = removeLets t
                        in Mlazy nt
removeLets (Mforce t) =  let nt = removeLets t
                         in Mforce nt
removeLets x =  x
 






----------------------------------------------------------------------------

createBinds :: [(String , Term)] -> [Binding]
createBinds [] = []
createBinds ((var , term) : ns) = Named (Ident var) var term : createBinds ns

-- Second Term is the initial one and we need it to use it as a key, so we pass it at the result.
replaceRec :: [(Integer , Term , Term)] -> UIDState [(String , (Integer , Term , Term))]
replaceRec [] = __IMPOSSIBLE__ -- ?
replaceRec ((i , t , k) : []) = pure $ ("ERROR" , (i , t , k)) : []
replaceRec ((i , t , k) : ts) =  do ar <- newUID
                                    let rs = map (replaceTr t (Mvar (Ident ar)) . (\(i , t , k) -> t))  ts
                                    nvs <- replaceRec
                                             (zip3 (map (\(i , _ , _) -> i) ts) rs (map (\(_ , _ , k) -> k) ts))
                                    pure $ (ar , (i , t , k)) : nvs





type UIDState = State (Integer , Integer)

-- We use this for the new Let vars.
newUID :: UIDState String
newUID = do
  s <- gets (show . fst)
  modify (\(a , b) -> (1 + a , b))
  pure $ "letId" ++ s

-- newOID must be called after the recursive part, so that first MApplys will get a lower number.
-- We use this to order possible lets. (ie MApplys).
newOID :: UIDState Integer
newOID = do
  s <- gets snd
  modify (\(a , b) -> (a , 1 + b))
  pure s





lintersect :: [M.Map Term (Term , Integer , Bool)] -> M.Map Term (Term , Integer , Bool)
lintersect (m : ms@(m2 : ms2)) = M.union (foldr (\a b -> M.intersection a b) m ms) (lintersect ms)
lintersect (m : []) = M.empty
lintersect [] = M.empty


-- This algorithm introduces more lets than are necessary.
-- TODO I need to clean the algorithm and if possible remove the unnecessary lets.


findCF :: Term -> UIDState (M.Map Term (Term , Integer , Bool) , Term)
findCF self@(Mvar i) = pure (M.empty , self)
findCF self@(Mlambda ids t) = do
                 (nr , _ , nself) <- inFilteredLets t (\k (_ , _ , c) -> let ui = findUsedIdents k
                                                                             int = intersect ui ids
                                                                         in (not $ null int) && c)
                                     
                 let nnr = M.filterWithKey (\k (_ , _ , _) -> let ui = findUsedIdents k
                                                                  int = intersect ui ids
                                                              in null int) nr
                 pure (nnr , Mlambda ids nself)
-- We need to perform findCF on a and bs when we create the let statement.
findCF self@(Mapply a bs) = do
                              rs <- mapM findCF (a : bs)
                              let inters = lintersect (map fst rs)
                                  newInters = M.map (\(a , b , c) -> (a , b , True)) inters
                                  all = foldr (\a b -> M.union (fst a) b)  M.empty rs
                                  -- newInters replaces inters here.
                                  nall = newInters `M.union` all
                                  (na , nbs) = (snd $ head rs , map snd (tail rs))
                                  nself = Mapply na nbs
                              noid <- newOID
                              pure (M.insert self (nself , noid , False) nall , nself )
findCF self@(Mlet bs t) = __IMPOSSIBLE__

-- We have to put all new let statements after the switch.
findCF self@(Mswitch ta tb) =  do
  (tmsa , nta) <- findCF ta
  rb <- mapM (singleCase . snd) tb
  let inters = foldr ((\x b -> M.union b (M.intersection tmsa x)) . fst) M.empty rb
      newInters = M.map (\(a , b , c) -> (a , b , True)) inters
      all = foldr (\a b -> M.union (fst a) b) tmsa rb
      -- newInters replaces inters here.
      nall = newInters `M.union` all
      ntb = zip (map fst tb) (map snd rb)
  pure (nall , Mswitch nta ntb)
  where
 
  singleCase :: Term -> UIDState (M.Map Term (Term , Integer , Bool) , Term)
  singleCase t = do
                    (nr , mr , nt) <- inFilteredLets t (\k (a , b , c) -> c) 
                    pure (M.union nr mr , nt)

findCF  (Muiop x y t) = do      (tms , nself) <- findCF  t
                                pure (tms , Muiop x y nself)
findCF  (Mbiop x y ta tb ) = do      (tmsa , nta) <- findCF  ta
                                     (tmsb , ntb) <- findCF  tb
                                     let inters = M.intersection tmsa tmsb
                                         newInters = M.map (\(a , b , c) -> (a , b , True)) inters
                                         all = M.union tmsa tmsb
                                         nall = newInters `M.union` all
                                     pure (nall , Mbiop x y nta ntb)
findCF  (Mconvert x y t) = do      (tms , nself) <- findCF  t
                                   pure (tms , Mconvert x y nself)
findCF  (Mblock x bs) =  do
                                 rs <- mapM findCF bs
                              
                                 let inters = lintersect (map fst rs)
                                     newInters = M.map (\(a , b , c) -> (a , b , True)) inters
                                     all = foldr (\a b -> M.union (fst a) b)  M.empty rs
                                     nall = newInters `M.union` all
                                 pure (nall , Mblock x (map snd rs))
findCF  (Mfield x t) =   do (tms , nself) <- findCF  t
                            pure (tms , Mfield x nself)

-- TODO Is this correct? I need to simplify the algorithm here.
findCF  self@(Mforce _)  = do noid <- newOID
                              pure (M.insert self (self , noid , False) M.empty , self)

-- IMPORTANT lazy evaluated expressions should not introduce lets statements.
findCF  x = pure (M.empty , x)



inFilteredLets :: Term -> (Term -> (Term , Integer , Bool) -> Bool)
              -> UIDState (M.Map Term (Term , Integer , Bool) , M.Map Term (Term , Integer , Bool) , Term)
inFilteredLets t ff = do
                  r <- findCF t
                  let psLets = M.filterWithKey ff (fst r)
                      lo = sort $ M.foldrWithKey (\k (a , b , c) l -> (b , a , k) : l) [] psLets
                      all = lo ++ [(0 , snd r , snd r)] -- last and first term should never be used for r.
                  rs <- replaceRec all
                  let bs = createBinds (zip (map fst rs) (map (\(_ , (_ , t , _)) -> t) (init rs)))
                  -- Return them with false so as to be possibly matched with higher statements.
                  let mr = M.fromList $ map (\(_ , (i , t , k)) -> (k , (t , i , False))) (init rs)
                      nr = M.difference (fst r) mr
                  pure (nr , mr , case bs of
                                    [] -> (\(_ , (_ , t , _)) -> t) (last rs)
                                    _ -> Mlet bs ((\(_ , (_ , t , _)) -> t) (last rs)))




introduceLets :: Term -> Term
introduceLets t =
  evalState (do 
               (_ , _ , nt) <- inFilteredLets t (\k (a , b , c) -> c)
               pure nt
            ) (0 , 0)






----------------------------------------------------------


removeLetsVar :: Term -> Term
removeLetsVar self@(Mvar i) = self
removeLetsVar (Mlambda a t) = let rm = removeLetsVar t
                              in Mlambda a rm
removeLetsVar (Mapply a bs) = let (na : nbs) = map removeLetsVar (a : bs)
                              in Mapply na nbs 
removeLetsVar (Mlet bs t) = let (trm , tkp) = partitionEithers (map rpl bs)
                                mt = foldr (\x y -> replaceTr (fst x) (snd x) y) t trm
                                ntkp = foldr (\x y -> map (\(Named id cn t) -> Named id cn (replaceTr (fst x) (snd x) t )) y) tkp trm
                                nt = removeLetsVar mt
                            in (case ntkp of
                                        [] -> nt
                                        _  -> Mlet ntkp nt)         where
  rpl :: Binding -> Either (Term , Term) Binding
  rpl (Named x _ (Mvar y)) = Left (Mvar x , Mvar y)
  rpl self@(Named x _ t) = Right self
  rpl (Recursive rs) = error "Let bindings cannot be recursive."
  
removeLetsVar (Mswitch ta tb) = let nta = removeLetsVar ta
                                    ntb = map (removeLetsVar . snd) tb
                                in Mswitch nta (zipWith (\(c , _) nb -> (c , nb)) tb ntb)
removeLetsVar (Muiop x y t) = let nt = removeLetsVar t
                              in Muiop x y nt
removeLetsVar (Mbiop x y ta tb ) = let nta = removeLetsVar ta
                                       ntb = removeLetsVar tb
                                   in Mbiop x y nta ntb
removeLetsVar (Mconvert x y t) = let nt = removeLetsVar t
                                 in Mconvert x y nt
removeLetsVar (Mblock x bs) = let nbs = map removeLetsVar bs
                              in Mblock x nbs
removeLetsVar (Mfield x t) = let nt = removeLetsVar t
                             in Mfield x nt
removeLetsVar x =  x




-----------------------------------------------------------


-- IMPORTANT : removeLets also protects against infinite loops in case of Coinduction.
-- so it is not just an optimization.
optimizeLets :: Term -> Term
optimizeLets r = r -- removeLetsVar $ introduceLets $ removeLets r

perfOptB :: (Term -> Term) -> [Binding] -> [Binding]
perfOptB f (Named id cn t : bs) = Named id cn (f t) : perfOptB f bs
perfOptB f (Recursive ys : bs) = Recursive (map (\(i , (cn , t)) -> (i , (cn , f t))) ys) : perfOptB f bs
perfOptB f [] = []

optimizeLetsB :: [Binding] -> [Binding]
optimizeLetsB bs = perfOptB optimizeLets bs


-- Erasure of all unnecessary code.
-- Each edge is an input or an output of a function.

-- Two edges that are put into the same set , correspond to the same value.
-- An input of a function can be an input of a function inside it.
-- An output of a function can be an input of another function.

-- We do not consider idents that are part of lambda , and let statements do not exist at this point.
-- As soon as we have the sets, we remove output edges that are alone.
-- If all output edges of a function are removed, we remove its inputs.
-- If an input of a function is not input to other functions inside it, we remove that input.
-- (We need to tag primitive functions.)

-- We do this iteratively untill we reach the minimum sets.
-- The main function or the exported functions are the ones we cannot touch, remove inputs or outputs.
-- (??For the main function , we need to take care that we do not remove IO??)

data Edge = Input Ident Ident | Output Ident Ident


