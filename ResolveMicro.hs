{-#LANGUAGE NamedFieldPuns, RecordWildCards,
GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, RankNTypes,
DeriveFunctor, TupleSections #-}

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

liftR x = R $ lift $ x
freshIdR = liftR freshId
insert :: (Lens Env (Map String Id)) -> A.Var -> (Id -> R a) -> R a
insert l y@(A.Var (_,x)) k = do
  v <- liftR $ freshFrom x
  insert' l y v (k v)

insert' l (A.Var (_,x)) v = local (upd l $ M.insert x v)

type Slice = Term' -> Term'

resolve :: A.Term -> Term'
resolve t =  runFreshM $ runReaderT (fromR $ resolveTerm t) emptyEnv

resolveTerm :: A.Term -> R (Term Id Id)
resolveTerm (A.Concl c) = do
  (c'id,c') <- resolveConstr c
  return $ c' $ Conc c'id
resolveTerm (A.Destr x c t) = do
  (c'id,c') <- resolveDestr c
  insert' con x c'id $ c' <$> resolveTerm t
-- resolveTerm (A.Destr x c t) = do
--   c' <- resolveDestr c x
--   c' <$> resolveTerm t
resolveTerm (A.Case x bs) = do
  (x'id,x') <- resolveDestr x
  bs' <- forM bs $ \(A.Br tag t) -> do
    (resolveTag tag,) <$> resolveTerm t
  return (x' $ Case x'id [Br tag t' | (tag,t') <- bs'])

resolveDestr :: A.Destr -> R (Id,Slice)
resolveDestr (A.V x) = do
  x' <- resolveVar hyp x
  case x' of
    Just x'' -> return (x'',id) 


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

resolveProj (A.First) = First
resolveProj (A.Second) = Second

resolveConstr :: A.Constr -> R (Id,Slice)
-- resolveConstr (A.Copy x) = Hyp <$> resolveVar con x
resolveConstr (A.Hyp h) = do
  r <- freshIdR
  (h'id,h') <- resolveDestr h
  return (r,h' . Constr r (Hyp h'id))
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
  return (r,Constr r (Fin $ mapM resolveTag ts))
resolveConstr (A.Univ (A.Nat (_,n))) = do
  r <- freshIdR
  return (r,Constr r (Universe $ read n))


resolveTag (A.T (A.Var (_,x))) = x
