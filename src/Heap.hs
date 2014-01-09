{-# LANGUAGE RecordWildCards, GADTs, OverloadedStrings #-}

module Heap where

import Control.Monad.RWS
import Control.Applicative

import Data.Bitraversable
import Data.Bifoldable
import Data.Bifunctor
import qualified Data.Map as M
import Data.Map (Map)
import Data.Generics.Genifunctors
import Data.Monoid

import Terms
import Ident
import Display
import TCM

emptyHeap :: Heap n r
emptyHeap = Heap M.empty M.empty M.empty M.empty M.empty M.empty

addCut' :: Ord n => n -> DeCo r -> Heap n r -> Heap n r
addCut' src trg h@Heap{..} = h{heapCuts = M.insert src trg heapCuts }

addAlias' :: Ord r => r -> r -> Heap n r -> Heap n r
addAlias' src trg h@Heap{..} = h{heapAlias = f <$> M.insert src trg heapAlias }
  where f x = if x == src then trg else x

addAliases' :: Ord r => [(r,r)] -> Heap n r -> Heap n r
addAliases' = foldr (.) id . map (uncurry addAlias')

addConstr' :: Ord n => n -> Constr n r -> Heap n r -> Heap n r
addConstr' src trg h@Heap{..} = h{heapConstr = M.insert src trg heapConstr }

addDestr' :: Ord r => Destr r -> n -> Heap n r -> Heap n r
addDestr' src trg h@Heap{..} = h{heapDestr = M.insert src trg heapDestr }

getAlias h x = M.findWithDefault x x h

addAliases :: [(Id,Id)] -> TC a -> TC a
addAliases [] k = k
addAliases as k = do
  tell ["Adding aliases: "<> pretty as]
  h <- addAliases' as <$> ask
  let hD' :: M.Map (Destr Id) [Hyp Id]
      applyAlias = getAlias $ heapAlias h
      hD' = M.mapKeysWith (++) (fmap applyAlias) $ fmap (:[]) $ heapDestr h
      myhead (x:_) = x
      hD'' = fmap myhead hD'
      classes = M.elems hD'
      aliases = [(x,y) | (x:xs) <- classes, y <- xs]
      -- apply aliases to redexes
      -- todo: remove orphan redexes?
      hC' :: M.Map (Hyp Id) (DeCo Id)
      hC' =  bimap (applyAlias <$>) id <$> heapCuts h
  local (\h2 -> h2 {heapDestr = hD'', heapAlias = heapAlias h, heapCuts = hC'}) $
    addAliases aliases k

addAlias :: Id -> Id -> TC a -> TC a
addAlias src trg = addAliases [(src,trg)]

aliasOf :: Id -> TC Id
aliasOf x = flip getAlias x . heapAlias <$> ask

-- | Look for some constructed value in the heap.
lookHeapC :: (r~Id,n~Id) => Conc n -> TC (Constr n r)
lookHeapC x = do
  lk <- M.lookup x . heapConstr <$> ask
  case lk of
    Nothing -> terr $ "Construction not found: " <> pretty x
    Just c -> return c
