{-# LANGUAGE GADTs #-}


module Terms where

import qualified Data.Map as M
import Data.Map(Map)

type Hyp a = a
type Conc a = a
type Tag = String

data Proj = First | Second
     deriving (Eq, Ord)

data Branch n r = Br Tag (Term n r)

data Term n r where
  Conc :: Conc r -> Term n r
  Destr :: Hyp n -> Destr r -> Term n r -> Term n r
  Case :: Hyp n -> [Branch n r] -> Term n r
  Constr :: Conc n -> Constr n r -> Term n r -> Term n r

data Destr r where
  Alias :: Hyp r -> Destr r
  App :: Hyp r -> Conc r -> Destr r
  Proj :: Hyp r -> Proj -> Destr r
  Cut :: Conc r -> Destr r
  
  -- | Hack to make sure that variables fixed to a tag become equal.
  Tag' :: Tag -> Destr r
    deriving (Eq, Ord)
data Constr n r where
  Done :: Hyp r -> Constr n r
  Alias' :: Conc r -> Constr n r
  Lam :: Hyp n -> Term  n r-> Constr n r
  Pi :: Hyp n -> Conc r -> Term n r -> Constr n r
  Sigma :: Hyp n -> Conc r -> Term n r -> Constr n r
  Pair :: Conc r -> Conc r -> Constr n r
  Tag :: Tag -> Constr n r
  Fin :: [Tag] -> Constr n r
  Universe :: Int -> Constr n r


data Entry n r where
  NH :: Hyp n -> Entry n r
  DH :: Hyp n -> Destr r -> Entry n r
  DC :: Conc n ->  Constr n r -> Entry n r
  CC :: Tag -> Hyp r -> Entry n r

data Heap n r = Heap { heapConstr :: Map (Conc n) (Constr n r)
                     , heapDestr :: Map (Destr r) (Hyp n)
                     , heapAlias :: Map r r
                     }



