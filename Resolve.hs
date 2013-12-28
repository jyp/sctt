{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables #-}
module Resolve where

import Terms
import qualified AbsNano as A
import Fresh
import Ident
import qualified Data.Map as M
import Data.Map (Map)
import Control.Monad.Reader
import Control.Applicative

data Env = Env {envHyp :: Map String Id,
                envCon :: Map String Id }

newtype R a = R {fromR :: ReaderT Env FreshM a}
  deriving (Functor, Applicative, Monad, MonadReader Env)

insertHyp :: String -> Id -> Env -> Env
insertHyp x v Env{..} = Env {envHyp = M.insert x v envHyp,.. }

lookupHyp :: String -> Env -> Maybe Id
lookupHyp x Env{..} = M.lookup x envHyp
 
insertCon :: String -> Id -> Env -> Env
insertCon x v Env{..} = Env {envCon = M.insert x v envCon,.. }

lookupCon :: String -> Env -> Maybe Id
lookupCon x Env{..} = M.lookup x envCon

resolveVar :: (String -> Env -> Maybe Id) -> A.Var -> R Id
resolveVar lk (A.Var (_,x)) = do
  v <- lk x <$> ask
  case v of
    Just i -> return i
    Nothing -> error $ "unknown identifier: " ++ x


  
resolveTerm :: A.Term -> R (Term Id Id)
resolveTerm (A.Constr x c t) = do
  c' <- resolveConstr
  insert insertHyp $ \x' -> Constr x' c' <$> resolveTerm t

resolveConstr :: A.Constr -> R (Constr Id Id)
resolveConstr (A.Hyp x) = resolveVar lookupHyp
