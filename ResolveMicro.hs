{-#LANGUAGE NamedFieldPuns, RecordWildCards,
GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, RankNTypes,
DeriveFunctor #-}

module Resolve where

import Terms
import qualified Micro.Abs as A
import Fresh
import Ident
import qualified Data.Map as M
import Data.Map (Map)
import Control.Monad.Reader
import Control.Applicative
import TCM

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
upd (L l) f a = fromI $ l (I . f) a

hyp,con :: Lens Env (Map String Id)
con = L $ \f (Env h c) -> fmap (Env h) (f c)
hyp = L $ \f (Env h c) -> fmap (flip Env c) (f h)
  
newtype R a = R {fromR :: ReaderT Env FreshM a}
  deriving (Functor, Applicative, Monad, MonadReader Env)

resolveVar :: (Lens Env (Map String Id)) -> A.Var -> R (Maybe Id)
resolveVar l (A.Var (_,x)) = M.lookup x . view l <$> ask

insert :: (Lens Env (Map String Id)) -> A.Var -> (Id -> R a) -> R a
insert l (A.Var (_,x)) k = do
  v <- R $ lift $ freshFrom x
  local (upd l $ M.insert x v) (k v)

type Slice = Term' -> Term'

resolve :: A.Term -> Term'
resolve t =  runFreshM $ runReaderT (fromR $ resolveTerm t) emptyEnv

resolveTerm :: A.Term -> R (Term Id Id)
resolveTerm (A.Concl x) = do
  i <- freshIdR
  c <- resolveConstr x 
  return $ c $ Conc i
resolveTerm (A.Constr x c t) = do
  c' <- resolveConstr c x
  c' <$> resolveTerm t

resolveDestr :: A.Destr -> Id -> R Slice
resolveTerm (A.Case x bs) = Case <$> resolveVar hyp x <*> (forM bs $ \(A.Br tag t) -> Br <$> resolveTag tag <*> resolveTerm t)
resolveConstr (A.Hyp x) = Hyp <$> resolveVar hyp x
resolveTerm (A.Concl x) = Conc <$> resolveVar con x
resolveDestr (A.Appl f x) = App <$> resolveVar hyp f <*> resolveVar con x
resolveDestr (A.Proj p f) r = do
  i <- freshIdR
  p' <- resolveDestr p i
  return (Destr r p' $ resolveProj f)
resolveDestr (A.Cut x t) = Cut <$> resolveVar con x <*> resolveVar con t

resolveProj (A.First) = First
resolveProj (A.Second) = Second

resolveConstr :: A.Constr -> Id -> R Slice
resolveTerm (A.Destr x d t) = do
  insert hyp x $ \x' -> Destr x' d' <$> resolveTerm t
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
