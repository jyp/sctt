{-#LANGUAGE NamedFieldPuns, RecordWildCards,
GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, RankNTypes,
DeriveFunctor #-}

module RM where
import Fresh
import Ident
import qualified Data.Map as M
import Data.Map (Map)
import Control.Monad.Reader
import Control.Applicative

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


