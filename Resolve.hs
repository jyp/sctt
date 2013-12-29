{-#LANGUAGE NamedFieldPuns, RecordWildCards,
GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, RankNTypes,
DeriveFunctor #-}

module Resolve where

import Terms
import qualified Nano.Abs as A
import Fresh
import Ident
import qualified Data.Map as M
import Data.Map (Map)
import Control.Monad.Reader
import Control.Applicative
import Eq (Term')
newtype K k a = K {fromK :: k} deriving Functor
newtype I a = I {fromI :: a} deriving Functor
data Env = Env {envHyp :: Map String Id,
                envCon :: Map String Id}
           deriving Show

emptyEnv = Env M.empty M.empty

newtype Lens a b = L {fromLens :: forall f. Functor f => (b -> f b) -> (a -> f a)}
view :: Lens a b -> a -> b
view (L g) r = fromK (g K r)

set :: forall a b. Lens a b -> b -> a -> a
set (L l) x r = runReader (l ((\_ -> ask) :: b -> Reader b b) r) x

upd :: Lens a b -> (b -> b) -> (a -> a)
upd (L l) f a = fromI $ l I a
hyp,con :: Lens Env (Map String Id)
con = L $ \f (Env h c) -> fmap (Env h) (f c)
hyp = L $ \f (Env h c) -> fmap (flip Env c) (f h)
  
newtype R a = R {fromR :: ReaderT Env FreshM a}
  deriving (Functor, Applicative, Monad, MonadReader Env)

resolveVar :: (Lens Env (Map String Id)) -> A.Var -> R Id
resolveVar l (A.Var (_,x)) = do
  v <- M.lookup x . view l <$> ask
  case v of
    Just i -> return i
    Nothing -> error $ "unknown identifier: " ++ x


insert :: (Lens Env (Map String Id)) -> A.Var -> (Id -> R a) -> R a
insert l (A.Var (_,x)) k = do
  v <- R $ lift $ freshId
  local (upd l $ M.insert x v) (k v)


resolve :: A.Term -> Term'
resolve t =  runFreshM $ runReaderT (fromR $ resolveTerm t) emptyEnv 

resolveTerm :: A.Term -> R (Term Id Id)
resolveTerm (A.Constr x c t) = do
  c' <- resolveConstr c
  insert con x $ \x' -> Constr x' c' <$> resolveTerm t
resolveTerm (A.Destr x d t) = do
  d' <- resolveDestr d
  insert hyp x $ \x' -> Destr x' d' <$> resolveTerm t
resolveTerm (A.Case x bs) = Case <$> resolveVar hyp x <*> (forM bs $ \(A.Br tag t) -> Br <$> resolveTag tag <*> resolveTerm t)

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
