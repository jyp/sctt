{-#LANGUAGE NamedFieldPuns, RecordWildCards,
GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, RankNTypes,
DeriveFunctor, TupleSections #-}

module Micro.Resolve where

import Terms
import qualified Micro.Abs as A
import Fresh
import Ident
import qualified Data.Map as M
import Data.Map (Map)
import Control.Monad.Reader
import Control.Applicative
import TCM
import RM

-- | Naming utilies

nameVar (A.Var (_,x)) = x

nameProj x A.First = x ++ ".1"
nameProj x A.Second = x ++ ".2"

nameLeft x = x ++ "ˡ"
nameRight x = x ++ "ʳ"

nameCut x _ = x

resolveVar :: (Lens Env (Map String Id)) -> A.Var -> R (Maybe Id)
resolveVar l (A.Var (_,x)) = M.lookup x . view l <$> ask

liftR x = R $ lift $ x
freshIdR = liftR freshId
freshFromR x = liftR $ freshFrom x
freshFromV :: A.Var -> R Id
freshFromV x = freshFromR $ nameVar x

insert :: (Lens Env (Map String Id)) -> A.Var -> (Id -> R a) -> R a
insert l y k = do
  v <- freshFromV y
  insert' l y v (k v)

insert' l (A.Var (_,x)) v = local (upd l $ M.insert x v)

type Slice = Term' -> Term'

resolve :: A.Module -> Either String (Term',Term')
resolve t = Right $ runFreshM $ runReaderT (fromR $ resolveModule t) emptyEnv

resolveModule :: A.Module -> R (Term',Term')
resolveModule (A.Module t1 t2) = (,) <$> resolveTerm t1 <*> resolveTerm t2

resolveTerm ::  A.Term -> R (Term Id Id)
resolveTerm x = resolveTerm' "top" x

resolveTerm' :: String -> A.Term -> R (Term Id Id)
resolveTerm' name (A.Destr x c t) = do
  (c'id,c') <- resolveDestr (nameVar x) c
  insert' hyp x c'id $ c' <$> resolveTerm' name t
resolveTerm' name (A.Concl c) = do
  (c'id,c') <- resolveConstr name c
  return $ c' $ Concl (Conc c'id)
resolveTerm' name (A.Constr x c t) = do
  (c'id,c') <- resolveConstr (nameVar x) c
  insert' con x c'id $ c' <$> resolveTerm' name t
resolveTerm' name (A.Split x y d t) = do
  (d'id,d') <- resolveDestr (nameVar x ++ nameVar y) d
  insert hyp x $ \x' ->
   insert hyp y $ \y' ->
    d' . Split x' y' d'id <$> resolveTerm' name t
resolveTerm' name (A.Case x bs) = do
  (x'id,x') <- resolveDestr name x
  bs' <- forM bs $ \(A.Br tag@(A.T tag') t) -> do
    (resolveTag tag,) <$> resolveTerm' (name ++ "|" ++ nameVar tag') t
  return (x' $ Case x'id [Br tag t' | (tag,t') <- bs'])

resolveDestr :: String -> A.DC -> R (Id,Slice)
resolveDestr _ (A.V x) = do
  x' <- resolveVar hyp x
  case x' of
    Just x'' -> return (x'',id)
    Nothing -> error $ "Unknown variable: " ++ show x

resolveDestr name (A.Appl f x) = do
  (f'id,f') <- resolveDestr (name ++ "ᶠ") f
  (x'id,x') <- resolveConstr (name ++ "ᵃ") x
  r <- freshFromR name
<<<<<<< HEAD
  return (r,f' . x' . Destr r (App f'id (Conc x'id)))
resolveDestr name (A.Proj p f) = do
  (p'id,p') <- resolveDestr (name ++ "ᵖ") p
  r <- freshFromR name
  return (r,p'.Destr r (Proj p'id $ resolveProj f))
=======
  return (r,f' . x' . Destr r (App f'id x'id))
-- resolveDestr name (A.Proj p f) = do
--   (p'id,p') <- resolveDestr (name ++ "ᵖ") p
--   r <- freshFromR name
--   return (r,p'.Destr r (Proj p'id $ resolveProj f))
>>>>>>> split
resolveDestr name (A.Cut x t) = do
  (x'id,x') <- resolveConstr (nameLeft name) x
  (t'id,t') <- resolveConstr (nameRight name) t
  r <- freshFromR name
  return (r, x'.t'.Destr r (Cut (Conc x'id) (Conc t'id)))
resolveDestr _ x = do
  error $ "Tryed to make an inline cut. (Cuts must be explicit via use of =)\n" ++ show x

resolveProj (A.First) = First
resolveProj (A.Second) = Second

resolveConstr :: String -> A.DC -> R (Id,Slice)
resolveConstr _name (A.V x) = do
  x' <- resolveVar con x
  case x' of
    Nothing -> embedHyp (nameVar x) (A.V x)
    Just x'' -> return (x'',id)
resolveConstr name (A.Rec x t) =
  insert hyp x $ \x' -> do
    r <- freshIdR
    t' <- resolveTerm' (name ++ "ʳᵉᶜ") t
    return (r,Constr (Conc r) (Rec x' t'))
resolveConstr name (A.Lam x t) =
  insert hyp x $ \x' -> do
    r <- freshFromR name
    t' <- resolveTerm' name t
    return (r,Constr (Conc r) (Lam x' t'))
resolveConstr name (A.Pi x c t) = do
  (c'id,c') <- resolveConstr (nameLeft name) c
  r <- freshFromR name
  insert hyp x $ \x' -> do
    t' <- resolveTerm' (nameRight name) t
    return (r,c' . Constr (Conc r) (Pi x' (Conc c'id) t'))
resolveConstr name (A.Fun c t) = do
  (c'id,c') <- resolveConstr (nameLeft name) c
  r <- freshFromR name
  t' <- resolveTerm' (nameRight name) t
  x' <- freshIdR
  return (r,c' . Constr (Conc r) (Pi x' (Conc c'id) t'))
resolveConstr name (A.Sigma x c t) = do
  (c'id,c') <- resolveConstr (nameLeft name) c
  r <- freshIdR
  insert hyp x $ \x' -> do
    t' <- resolveTerm' (nameRight name) t
    return (r,c' . Constr (Conc r) (Sigma x' (Conc c'id) t'))
resolveConstr name (A.Pair a b) = do
  (a'id,a') <- resolveConstr (name ++ ".1") a
  (b'id,b') <- resolveConstr (name ++ ".2") b
  r <- freshIdR
  return (r,a'.b'.Constr (Conc r) (Pair (Conc a'id) (Conc b'id)))
resolveConstr name (A.Tag t) = do
  r <- freshFromR name
  return (r,Constr (Conc r) (Tag $ resolveTag t))
resolveConstr name (A.Fin ts) = do
  r <- freshFromR name
  return (r,Constr (Conc r) (Fin $ map resolveTag ts))
resolveConstr name (A.Univ (A.Nat (_,n))) = do
  r <- freshFromR name
  return (r,Constr (Conc r) (Universe $ read n))
resolveConstr name h = embedHyp name h

embedHyp :: String -> A.DC -> R (Id, Slice)
embedHyp name h = do
  r <- freshFromR name
  (h'id,h') <- resolveDestr name h
  return (r,h' . Constr (Conc r) (Hyp h'id))


resolveTag (A.T (A.Var (_,x))) = x
