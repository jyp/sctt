{-#LANGUAGE NamedFieldPuns, RecordWildCards,
GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, RankNTypes,
DeriveFunctor #-}

module Nano.Resolve where

import Terms
import qualified Nano.Abs as A
import Fresh
import Ident
import qualified Data.Map as M
import Data.Map (Map)
import Control.Monad.Reader
import Control.Applicative
import TCM
import RM

resolveVar :: (Lens Env (Map String Id)) -> A.Var -> R Id
resolveVar l (A.Var (_,x)) = do
  env <- ask
  let v = M.lookup x . view l $ env
  case v of
    Just i -> return i
    Nothing -> error $
                 "env = " ++ show env ++ "\n" ++
                 "unknown identifier: " ++ x


insert :: (Lens Env (Map String Id)) -> A.Var -> (Id -> R a) -> R a
insert l (A.Var (_,x)) k = do
  v <- R $ lift $ freshFrom x
  local (upd l $ M.insert x v) (k v)


resolve :: A.Module -> Either String (Term',Term')
resolve t = Right $ runFreshM $ runReaderT (fromR $ resolveModule t) emptyEnv

resolveModule :: A.Module -> R (Term',Term')
resolveModule (A.Module t1 t2) = (,) <$> resolveTerm t1 <*> resolveTerm t2

resolveTerm :: A.Term -> R (Term Id Id)
resolveTerm (A.Constr x c t) = do
  c' <- resolveConstr c
  insert con x $ \x' -> Constr x' c' <$> resolveTerm t
resolveTerm (A.Destr x d t) = do
  d' <- resolveDestr d
  insert hyp x $ \x' -> Destr x' d' <$> resolveTerm t
resolveTerm (A.Case x bs) = Case <$> resolveVar hyp x <*> (forM bs $ \(A.Br tag t) -> Br <$> resolveTag tag <*> resolveTerm t)
resolveTerm (A.Concl x) = Concl <$> resolveVar con x

resolveDestr :: A.Destr -> R (Destr Id)
resolveDestr (A.Appl f x) = App <$> resolveVar hyp f <*> resolveVar con x
resolveDestr (A.Proj p f) = Proj <$> resolveVar hyp p <*> pure (resolveProj f)
resolveDestr (A.Cut x t) = Cut <$> resolveVar con x <*> resolveVar con t

resolveProj (A.First) = First
resolveProj (A.Second) = Second

resolveConstr :: A.Constr -> R (Constr Id Id)
resolveConstr (A.Hyp x) = Hyp <$> resolveVar hyp x
resolveConstr (A.Lam x t) = insert hyp x $ \x' ->
  Lam x' <$> resolveTerm t
resolveConstr (A.Pi x c t) = insert hyp x $ \x' ->
  Pi x' <$> resolveVar con c <*> resolveTerm t
resolveConstr (A.Pair a b) = Pair <$> resolveVar con a <*> resolveVar con b
resolveConstr (A.Sigma x c t) = insert hyp x $ \x' ->
  Sigma x' <$> resolveVar con c <*> resolveTerm t
resolveConstr (A.Tag t) = Tag <$> resolveTag t
resolveConstr (A.Fin ts) = Fin <$> mapM resolveTag ts
resolveConstr (A.Univ (A.Nat (_,n))) = Universe <$> pure (read n)


resolveTag (A.T (A.Var (_,x))) = pure x
