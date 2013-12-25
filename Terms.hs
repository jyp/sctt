{-# LANGUAGE GADTs, DeriveFunctor, TemplateHaskell #-}


module Terms where

import Data.Bitraversable
import Data.Bifoldable
import Data.Bifunctor
import qualified Data.Map as M
import Data.Map(Map)
import Data.Generics.Genifunctors

type Hyp a = a
type Conc a = a
type Tag = String

data Proj = First | Second
     deriving (Eq, Ord)

data Branch n r = Br Tag (Term n r)

instance Bifoldable Term where  bifoldMap = bifoldMapDefault
instance Bifunctor Term where  bimap = bimapDefault
instance Bitraversable Term where  bitraverse = $(genTraverse ''Term)

data Term n r where
  Destr :: Hyp n -> Destr r -> Term n r -> Term n r
  Case :: Hyp n -> [Branch n r] -> Term n r
  Constr :: Conc n -> Constr n r -> Term n r -> Term n r
  Conc :: Conc r -> Term n r  -- ^ Conclude

data Destr r where
  -- Alias :: Hyp r -> Destr r -- not needed in terms.
  App :: Hyp r -> Conc r -> Destr r
  Proj :: Hyp r -> Proj -> Destr r
  Cut :: Conc r -> Destr r
    deriving (Eq, Ord, Functor)

data Constr n r where
  -- Alias' :: Conc r -> Constr n r
  Hyp :: Hyp r -> Constr n r
  Lam :: Hyp n -> Term n r -> Constr n r
  Pi :: Hyp n -> Conc r -> Term n r -> Constr n r
  Sigma :: Hyp n -> Conc r -> Term n r -> Constr n r
  Pair :: Conc r -> Conc r -> Constr n r
  Tag :: Tag -> Constr n r
  Fin :: [Tag] -> Constr n r
  Universe :: Int -> Constr n r

-- data Entry n r where
--   NH :: Hyp n -> Entry n r
--   DH :: Hyp n -> Destr r -> Entry n r
--   DC :: Conc n ->  Constr n r -> Entry n r
--   CC :: Tag -> Hyp r -> Entry n r

type DC n r = Either (Destr r) (Constr n r)

data Heap n r = Heap { heapConstr :: Map (Conc n) (DC n r)
                     , heapCuts :: Map (Hyp n) (Conc r)
                     , heapDestr :: Map (Destr r) (Hyp n)
                     , heapAlias :: Map r r
                     , context :: Map r (Conc r) -- ^ types
                     }

emptyHeap = Heap M.empty M.empty M.empty M.empty M.empty

