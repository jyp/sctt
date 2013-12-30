{-# LANGUAGE GADTs, DeriveFunctor, TemplateHaskell, OverloadedStrings #-}


module Terms where

import Data.Bitraversable
import Data.Bifoldable
import Data.Bifunctor
import qualified Data.Map as M
import Data.Map (Map)
import Data.Generics.Genifunctors
import Display
import Data.Monoid

type Hyp a = a
type Conc a = a
type Tag = String

data Proj = First | Second
     deriving (Eq, Ord, Show)

instance Pretty Proj where
   pretty Terms.First = ".1"
   pretty Terms.Second = ".2"

data Branch n r = Br Tag (Term n r)
    deriving (Show)

instance Bifoldable Term where  bifoldMap = bifoldMapDefault
instance Bifunctor Term where  bimap = bimapDefault
instance Bitraversable Term where  bitraverse = $(genTraverse ''Term)

data Term n r where
  Destr :: Hyp n -> Destr r -> Term n r -> Term n r
  Case :: Hyp n -> [Branch n r] -> Term n r
  Constr :: Conc n -> Constr n r -> Term n r -> Term n r
  Conc :: Conc r -> Term n r  -- ^ Conclude
    deriving (Show)

data Destr r where
  App :: Hyp r -> Conc r -> Destr r
  Proj :: Hyp r -> Proj -> Destr r
  Cut :: Conc r -> Conc r {-^ the type-} -> Destr r
    deriving (Show, Eq, Ord, Functor)

instance Pretty r => Pretty (Destr r) where
  pretty (App f x) = pretty f <> " " <> pretty x
  pretty (Proj x p) = pretty x <> pretty p
  pretty (Cut x t) = pretty x <> ":" <> pretty t

data Constr n r where
  Hyp :: Hyp r -> Constr n r
  Lam :: Hyp n -> Term n r -> Constr n r
  Pi :: Hyp n -> Conc r -> Term n r -> Constr n r
  Sigma :: Hyp n -> Conc r -> Term n r -> Constr n r
  Pair :: Conc r -> Conc r -> Constr n r
  Tag :: Tag -> Constr n r
  Fin :: [Tag] -> Constr n r
  Universe :: Int -> Constr n r
    deriving (Show)

type DC n r = Either (Destr r) (Constr n r)

data Heap n r = Heap { heapConstr :: Map (Conc n) (DC n r)
                     , heapCuts :: Map (Hyp n) (Conc r)
                     , heapDestr :: Map (Destr r) (Hyp n)
                     , heapAlias :: Map r r
                     , context :: Map n (Conc r) -- ^ types
                     }

emptyHeap :: Heap n r
emptyHeap = Heap M.empty M.empty M.empty M.empty M.empty

