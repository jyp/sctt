{-# LANGUAGE RecordWildCards, GADTs, OverloadedStrings, TypeSynonymInstances, FlexibleInstances, RecordWildCards  #-}

module Heap (emptyHeap, addCut,lookHeapC,getAlias,addConstr,enter,addDestr,addAlias',aliasOf,pConc,pHyp,addAlias) where

import Control.Monad.RWS
import Control.Applicative

import Data.Bifunctor
import qualified Data.Map as M

import Terms
import Ident
import Display
import TCM

emptyHeap :: Heap n r
emptyHeap = Heap 0 M.empty M.empty M.empty M.empty M.empty

enter :: TC a -> TC a
enter = local (\h@Heap{..} -> h {dbgDepth = dbgDepth + 1})

addCut :: (Id~n,Id~r,Ord n) => n -> DeCo r -> TC a -> TC a
addCut src trg k =
  case trg of
    Right c -> do c' <- lookHeapC c
                  case c' of
                    Hyp trg' -> addAlias src trg' k
                    _ -> def
    _ -> def
  where def = local (addCut' src trg) k

addCut' :: Ord n => n -> DeCo r -> Heap n r -> Heap n r
addCut' src trg h@Heap{..} = h{heapCuts = M.insert src trg heapCuts }

addAlias' :: Ord r => r -> r -> Heap n r -> Heap n r
addAlias' src trg h@Heap{..} = h{heapAlias = f <$> M.insert src trg heapAlias }
  where f x = if x == src then trg else x

addAliases' :: Ord r => [(r,r)] -> Heap n r -> Heap n r
addAliases' = foldr (.) id . map (uncurry addAlias')

addConstr' :: Ord n => Conc n -> Constr n r -> Heap n r -> Heap n r
addConstr' src trg h@Heap{..} = h{heapConstr = M.insert src trg heapConstr }

addDestr' :: Ord r => Destr r -> n -> Heap n r -> Heap n r
addDestr' src trg h@Heap{..} = h{heapDestr = M.insert src trg heapDestr }

getAlias h x = M.findWithDefault x x h

addAliases :: [(Id,Id)] -> TC a -> TC a
addAliases [] k = k
addAliases as k = do
  report $ ("Adding aliases:" $$+ pretty as)
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


addDestr :: Hyp Id -> Destr Id -> TC a -> TC a
addDestr x (Cut c _ct) k = local (addCut' x $ Right c) k
addDestr x d k = do
  h <- ask
  let d' = getAlias (heapAlias h) <$> d
  report ("Adding destr."
        $$+ pretty x <+> "="
        $$+ pretty d  <+> "; aliased to" <+> pretty d')
  local (addCut' x $ Left d') $ case M.lookup d' (heapDestr h) of
     Just y -> addAlias y x k
     Nothing -> local (addDestr' d' x) k

-- | return true if fizzled, otherwise call the continuation.
addConstr :: Monoid a => Conc Id -> Constr' -> TC a -> TC a
addConstr x c k = do
  report ("Adding construction" $$++ pretty x <+> "=" $$+ pretty c)
  hC <- heapConstr <$> ask
  hA <- heapAlias <$> ask
  case c of
    Tag t | Just (Tag t') <- M.lookup x hC -> if t /= t' then return mempty else k
    _ -> local (addConstr' x $ getAlias hA <$> c) k

instance Monoid Bool where
  mempty = True
  mappend = (&&)

-- | Pretty printing

class Prettier a where
  prettier :: a -> TC Doc

pConc :: Conc Id -> TC Doc
pConc x = prettier =<< lookHeapC x

pHyp :: Hyp Id -> TC Doc
pHyp x = do
  h <- ask
  let lk = M.lookup (getAlias (heapAlias h) x) $ heapCuts h
  case lk of
    Nothing -> return $ pretty x
    Just (Right c) -> pConc c
    Just (Left d) -> prettier d

instance Prettier Term' where
  prettier (Concl c) = pConc c
  prettier (Destr h d t) = addDestr h d $ prettier t
  prettier (Constr x c t) = addConstr x c $ prettier t
  prettier (Split x y z t) = do
    z' <- pHyp z
    t' <- prettier t
    return $ ("split " <> z' <> "into " <> pretty x <> "," <> pretty y $$ t')
  prettier (Case x bs) = do
    bs' <- mapM prettier bs
    h <- pHyp x
    return $ ("case" <+> h <+> "of {") $$+ (sep $ punctuate "." $ bs') $$ "}"

instance Prettier Constr' where
  prettier (Hyp h) = pHyp h
  prettier (Lam x b) = do
    b' <- prettier b
    return $ ("\\" <> pretty x <> " ->") $$+ b'
  prettier (Pi x t b) = do
    t' <- pConc t
    b' <- prettier b
    return $ (parens (pretty x <>":"<> t') <+> "->") $$+ b'
  prettier (Sigma x t b) = do
    t' <- pConc  t
    b' <- prettier b
    return $ parens (pretty x <>":"<> t') <> " × " <> b'
  prettier (Pair a b) = do
    a' <- pConc  a
    b' <- pConc  b
    return $ parens $ a' $$+ "," $$+ b'
  prettier x = return $ pretty x

instance Prettier Destr' where
  prettier (App f x) = do
    f' <- pHyp f
    x' <- pConc x
    return $ f' <+> x'
  prettier (Cut x t) = do
    x' <- pConc x
    t' <- pConc t
    return $ x' <+> ":" <+> t'

instance Prettier Branch' where
  prettier (Br tag t) = (\x -> ("'" <> text tag <> " ->") $$+ x) <$> prettier t
