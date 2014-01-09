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

resolveVar :: (Lens Env (Map String Id)) -> A.Var -> R (Maybe Id)
resolveVar l (A.Var (_,x)) = M.lookup x . view l <$> ask

liftR x = R $ lift $ x
freshIdR = liftR freshId
insert :: (Lens Env (Map String Id)) -> A.Var -> (Id -> R a) -> R a
insert l y@(A.Var (_,x)) k = do
  v <- liftR $ freshFrom x
  insert' l y v (k v)

insert' l (A.Var (_,x)) v = local (upd l $ M.insert x v)

type Slice = Term' -> Term'

resolve :: A.Module -> Either String (Term',Term')
resolve t = Right $ runFreshM $ runReaderT (fromR $ resolveModule t) emptyEnv

resolveModule :: A.Module -> R (Term',Term')
resolveModule (A.Module t1 t2) = (,) <$> resolveTerm t1 <*> resolveTerm t2

resolveTerm :: A.Term -> R (Term Id Id)
resolveTerm (A.Concl c) = do
  (c'id,c') <- resolveConstr c
  return $ c' $ Conc c'id
resolveTerm (A.Destr x c t) = do
  (c'id,c') <- resolveDestr c
  insert' hyp x c'id $ c' <$> resolveTerm t
  -- here we should change c'id to contain the string x.
resolveTerm (A.Case x bs) = do
  (x'id,x') <- resolveDestr x
  bs' <- forM bs $ \(A.Br tag t) -> do
    (resolveTag tag,) <$> resolveTerm t
  return (x' $ Case x'id [Br tag t' | (tag,t') <- bs'])

resolveDestr :: A.DC -> R (Id,Slice)
resolveDestr (A.V x) = do
  x' <- resolveVar hyp x
  case x' of
    Just x'' -> return (x'',id) 
    Nothing -> error $ "Unknown variable: " ++ show x

resolveDestr (A.Appl f x) = do
  (f'id,f') <- resolveDestr f
  (x'id,x') <- resolveConstr x
  r <- freshIdR
  return (r,f' . x' . Destr r (App f'id x'id))
resolveDestr (A.Proj p f) = do
  (p'id,p') <- resolveDestr p
  r <- freshIdR
  return (r,p'.Destr r (Proj p'id $ resolveProj f))
resolveDestr (A.Cut x t) = do
  (x'id,x') <- resolveConstr x
  (t'id,t') <- resolveConstr t
  r <- freshIdR
  return (r, x'.t'.Destr r (Cut x'id t'id))
resolveDestr x = do
  error $ "Tryed to make an inline cut. (Cuts must be explicit via use of =)\n" ++ show x

resolveProj (A.First) = First
resolveProj (A.Second) = Second

resolveConstr :: A.DC -> R (Id,Slice)
resolveConstr (A.Lam x t) =
  insert hyp x $ \x' -> do
    r <- freshIdR
    t' <- resolveTerm t
    return (r,Constr r (Lam x' t'))
resolveConstr (A.Pi x c t) = do
  (c'id,c') <- resolveConstr c
  r <- freshIdR
  insert hyp x $ \x' -> do
    t' <- resolveTerm t
    return (r,c' . Constr r (Pi x' c'id t'))
resolveConstr (A.Fun c t) = do
  (c'id,c') <- resolveConstr c
  r <- freshIdR
  t' <- resolveTerm t
  x' <- freshIdR
  return (r,c' . Constr r (Pi x' c'id t'))
resolveConstr (A.Sigma x c t) = do
  (c'id,c') <- resolveConstr c
  r <- freshIdR
  insert hyp x $ \x' -> do
    t' <- resolveTerm t
    return (r,c' . Constr r (Sigma x' c'id t'))
resolveConstr (A.Pair a b) = do
  (a'id,a') <- resolveConstr a
  (b'id,b') <- resolveConstr b
  r <- freshIdR
  return (r,a'.b'.Constr r (Pair a'id b'id))
resolveConstr (A.Tag t) = do
  r <- freshIdR
  return (r,Constr r (Tag $ resolveTag t))
resolveConstr (A.Fin ts) = do 
  r <- freshIdR
  return (r,Constr r (Fin $ map resolveTag ts))
resolveConstr (A.Univ (A.Nat (_,n))) = do
  r <- freshIdR
  return (r,Constr r (Universe $ read n))
resolveConstr h = do
  r <- freshIdR
  (h'id,h') <- resolveDestr h
  return (r,h' . Constr r (Hyp h'id))


resolveTag (A.T (A.Var (_,x))) = x
