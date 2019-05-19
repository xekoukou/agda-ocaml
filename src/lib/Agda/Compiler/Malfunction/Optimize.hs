{-# OPTIONS_GHC -Wall -Wno-name-shadowing -Wno-unused-matches#-}
module Agda.Compiler.Malfunction.Optimize (optimizeLetsB , replaceTr) where

import Agda.Compiler.Malfunction.AST
import Agda.Compiler.Malfunction.EraseDefs
import Data.List
import Data.Either
import qualified Data.Map.Strict as M

import Control.Monad.State


caseEq :: Term -> Term -> Term -> Term -> Term
caseEq rt ar t ot = case rt == t of
                     True -> ar
                     False -> ot

replaceTr :: Term -> Term -> Term -> Term
replaceTr rt ar self@(Mvar i) = caseEq rt ar self self
replaceTr rt ar self@(Mlambda a t) = caseEq rt ar self $ Mlambda a (replaceTr rt ar t)
replaceTr rt ar self@(Mapply a bs) = caseEq rt ar self $ let (na : nbs) = map (replaceTr rt ar) (a : bs)
                                                         in Mapply na nbs 
replaceTr rt ar self@(Mlet bs t) =  caseEq rt ar self $  let nt = replaceTr rt ar t
                                       in Mlet (map (rpl rt ar) bs) nt where
  rpl :: Term -> Term -> Binding -> Binding
  rpl rt ar (Unnamed t) = Unnamed $ replaceTr rt ar t
  rpl rt ar (Named x t) = Named x $ replaceTr rt ar t
  rpl rt ar (Recursive rs) = Recursive (zipWith (\x y -> (fst x , y)) rs (map (replaceTr rt ar . snd) rs))
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
replaceTr rt ar self@(Mvecnew x ta tb) =  caseEq rt ar self $
                                            let nta = replaceTr rt ar ta
                                                ntb = replaceTr rt ar tb
                                            in Mvecnew x nta ntb
replaceTr rt ar self@(Mvecget x ta tb) =  caseEq rt ar self $
                                            let nta = replaceTr rt ar ta
                                                ntb = replaceTr rt ar tb
                                            in Mvecget x nta ntb
replaceTr rt ar self@(Mvecset x ta tb tc) =  caseEq rt ar self $
                                               let nta = replaceTr rt ar ta
                                                   ntb = replaceTr rt ar tb
                                                   ntc = replaceTr rt ar tc
                                               in Mvecset x nta ntb ntc
replaceTr rt ar self@(Mveclen x t) =  caseEq rt ar self $
                                        let nt = replaceTr rt ar t
                                        in Mveclen x nt
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


replaceTrL :: [(Term , Term)] -> Term -> Term
replaceTrL ((x , nx) : ms) t = let (nt : rnms) = map (replaceTr x nx) (t : map snd ms)
                               in replaceTrL (zip (map fst ms) rnms) nt
replaceTrL [] t = t

-----------------------------------------------------------


--- We remove let statements . According to a treeless comment https://github.com/agda/agda/blob/master/src/full/Agda/Syntax/Treeless.hs#L44 , this is perfectly reasonable.

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
  rpl (Unnamed t) = error "Let bindings should have a name."
  rpl (Named x t) = (Mvar x , t)
  rpl (Recursive rs) = error "Let bindings cannot be recursive."
  
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
removeLets (Mvecnew x ta tb) = let nta = removeLets ta
                                   ntb = removeLets tb
                               in Mvecnew x nta ntb
removeLets (Mvecget x ta tb) = let nta = removeLets ta
                                   ntb = removeLets tb
                               in Mvecget x nta ntb
removeLets (Mvecset x ta tb tc) = let nta = removeLets ta
                                      ntb = removeLets tb
                                      ntc = removeLets tc
                                  in Mvecset x nta ntb ntc
removeLets (Mveclen x t) = let nt = removeLets t
                           in Mveclen x nt
removeLets (Mblock x bs) = let nbs = map removeLets bs
                           in Mblock x nbs
removeLets (Mfield x t) = let nt = removeLets t
                          in Mfield x nt
removeLets x =  x
 





----------------------------------------------------------------------------

createBinds :: [(String , Term)] -> [Binding]
createBinds [] = []
createBinds ((var , term) : ns) = Named (Ident var) term : createBinds ns

-- Second Term is the initial one and we need it to use it as a key, so we pass it at the result.
replaceRec :: [(Integer , Term , Term)] -> UIDState [(String , (Integer , Term , Term))]
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
findCF self@(Mlet bs t) = error "We have removed all let statements"

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
findCF  (Mvecnew x ta tb) =  do      (tmsa , nta) <- findCF  ta
                                     (tmsb , ntb) <- findCF  tb
                                     let inters = M.intersection tmsa tmsb
                                         newInters = M.map (\(a , b , c) -> (a , b , True)) inters
                                         all = M.union tmsa tmsb
                                         nall = newInters `M.union` all
                                     pure (nall , Mvecnew x nta ntb)
findCF  (Mvecget x ta tb) = do      (tmsa , nta) <- findCF  ta
                                    (tmsb , ntb) <- findCF  tb
                                    let inters = M.intersection tmsa tmsb
                                        newInters = M.map (\(a , b , c) -> (a , b , True)) inters
                                        all = M.union tmsa tmsb
                                        nall = newInters `M.union` all
                                    pure (nall , Mvecget x nta ntb)
findCF  (Mvecset x ta tb tc) =  do      (tmsa , nta) <- findCF  ta
                                        (tmsb , ntb) <- findCF  tb
                                        (tmsc , ntc) <- findCF  tc
                                        let inters = M.intersection (M.intersection tmsa tmsb) tmsc
                                            newInters = M.map (\(a , b , c) -> (a , b , True)) inters
                                            all = M.union (M.union tmsa tmsb) tmsc
                                            nall = newInters `M.union` all
                                        pure (nall , Mvecset x nta ntb ntc)
findCF  (Mveclen x t) =  do (tms , nself) <- findCF  t
                            pure (tms , Mveclen x nself)
findCF  (Mblock x bs) =  do
                                 rs <- mapM findCF bs
                              
                                 let inters = lintersect (map fst rs)
                                     newInters = M.map (\(a , b , c) -> (a , b , True)) inters
                                     all = foldr (\a b -> M.union (fst a) b)  M.empty rs
                                     nall = newInters `M.union` all
                                 pure (nall , Mblock x (map snd rs))
findCF  (Mfield x t) =   do (tms , nself) <- findCF  t
                            pure (tms , Mfield x nself)
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
                                ntkp = foldr (\x y -> map (\(Named id t) -> Named id (replaceTr (fst x) (snd x) t )) y) tkp trm
                                nt = removeLetsVar mt
                            in (case ntkp of
                                        [] -> nt
                                        _  -> Mlet ntkp nt)         where
  rpl :: Binding -> Either (Term , Term) Binding
  rpl (Unnamed t) = error "Let bindings should have a name."
  rpl (Named x (Mvar y)) = Left (Mvar x , Mvar y)
  rpl self@(Named x t) = Right self
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
removeLetsVar (Mvecnew x ta tb) = let nta = removeLetsVar ta
                                      ntb = removeLetsVar tb
                                  in Mvecnew x nta ntb
removeLetsVar (Mvecget x ta tb) = let nta = removeLetsVar ta
                                      ntb = removeLetsVar tb
                                  in Mvecget x nta ntb
removeLetsVar (Mvecset x ta tb tc) = let nta = removeLetsVar ta
                                         ntb = removeLetsVar tb
                                         ntc = removeLetsVar tc
                                     in Mvecset x nta ntb ntc
removeLetsVar (Mveclen x t) = let nt = removeLetsVar t
                              in Mveclen x nt
removeLetsVar (Mblock x bs) = let nbs = map removeLetsVar bs
                              in Mblock x nbs
removeLetsVar (Mfield x t) = let nt = removeLetsVar t
                             in Mfield x nt
removeLetsVar x =  x




-----------------------------------------------------------


-- Used in Functions.
optimizeLets :: Term -> Term
optimizeLets (Mlambda ids t) = Mlambda ids (removeLetsVar $ introduceLets $ removeLets t)
optimizeLets (Mblock tag tms) = Mblock tag (map (removeLetsVar . introduceLets . removeLets) tms)
optimizeLets r = r



optimizeLetsB :: [Binding] -> [Binding]
optimizeLetsB (Named id t : bs) = Named id (optimizeLets t) : optimizeLetsB bs
optimizeLetsB (Recursive ys : bs) = Recursive (zip (map fst ys) (map (optimizeLets . snd) ys)) : optimizeLetsB bs
optimizeLetsB (_ : bs) = error "Unnamed binding?"
optimizeLetsB [] = []
