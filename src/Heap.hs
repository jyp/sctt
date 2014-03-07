{-# LANGUAGE RecordWildCards, GADTs, OverloadedStrings, TypeSynonymInstances, FlexibleInstances, RecordWildCards  #-}

module Heap (emptyHeap, addDef,addCut,lookHeapC,getAlias,addConstr, addConstr', addDestr', enter,addDestr,addAlias',aliasOf,pConc,pHyp,addAlias) where

import Control.Monad.RWS
import Control.Applicative

import Data.Bifunctor
import qualified Data.Map as M

import Terms
import Ident
import Display
import TCM
import Fresh

emptyHeap :: Heap n r
emptyHeap = Heap 0 M.empty M.empty M.empty M.empty M.empty M.empty

enter :: TC a -> TC a
enter = local (\h@Heap{..} -> h {dbgDepth = dbgDepth + 1})

addDef :: (Monoid a,Id~n,Id~r,Ord n) => Hyp n -> Constr n r -> TC a -> TC a
addDef h c k = do
  case c of
    Hyp h' -> addAlias h h' k
    _ -> do
      c' <- Conc <$> liftTC (refreshId h)
      addConstr c' c $ local (addCut' h (Right c')) k

addElimDef :: (Monoid a,Id~n,Id~r,Ord n) => Hyp n -> Destr n -> TC a -> TC a
addElimDef h d = local (addCut' h $ Left d)

addCut :: (Id~n,Id~r,Ord n) => Hyp n -> Conc r -> TC a -> TC a
addCut src c k = do
  report $ "adding cut: " <> pretty src <> " => " <> pretty c
  c' <- lookHeapC c
  case c' of
    Hyp h' -> addAlias src h' k
    _ -> local (addCut' src $ Right c) k

addCut' :: Ord n => n -> DeCo r -> Heap n r -> Heap n r
addCut' src trg h@Heap{..} = h{heapDestr = M.insert src trg heapDestr }

addAlias' :: Ord r => r -> r -> Heap n r -> Heap n r
addAlias' src trg h@Heap{..} = h{heapAlias = f <$> M.insert src trg heapAlias }
  where f x = if x == src then trg else x

addAliases' :: Ord r => [(r,r)] -> Heap n r -> Heap n r
addAliases' = foldr (.) id . map (uncurry addAlias')

addConstr' :: Ord n => Conc n -> Constr n r -> Heap n r -> Heap n r
addConstr' src trg h@Heap{..} = h{heapConstr = M.insert src trg heapConstr }

addRevConstr' :: (Ord n, Ord r) => Constr n r -> Conc n -> Heap n r -> Heap n r
addRevConstr' src trg h@Heap{..} = h{heapRevConstr = M.insert src trg heapRevConstr }

addDestr' :: Ord r => Destr r -> n -> Heap n r -> Heap n r
addDestr' src trg h@Heap{..} = h{heapRevDestr = M.insert src trg heapRevDestr }

getAlias h x = M.findWithDefault x x h

addAliases :: [(Id,Id)] -> TC a -> TC a
addAliases [] k = k
addAliases as k = do
  report $ ("Adding aliases:" $$+ pretty as)
  h <- addAliases' as <$> ask
  let hD' :: M.Map (Destr Id) [Hyp Id]
      applyAlias = getAlias $ heapAlias h
      hD' = M.mapKeysWith (++) (fmap applyAlias) $ fmap (:[]) $ heapRevDestr h
      myhead (x:_) = x
      hD'' = fmap myhead hD'
      classes = M.elems hD'
      aliases = [(x,y) | (x:xs) <- classes, y <- xs]
      -- apply aliases to redexes
      -- todo: remove orphan redexes?
      hC' :: M.Map (Hyp Id) (DeCo Id)
      hC' =  bimap (applyAlias <$>) id <$> heapDestr h
  local (\h2 -> h2 {heapRevDestr = hD'', heapAlias = heapAlias h, heapDestr = hC'}) $
    addAliases aliases k

addAlias :: Id -> Id -> TC a -> TC a
addAlias src trg = addAliases [(src,trg)]

aliasOf x = flip getAlias x . heapAlias <$> ask

-- | Look for some constructed value in the heap.
lookHeapC :: (r~Id,n~Id) => Conc n -> TC (Constr n r)
lookHeapC x = do
  h <- ask
  x' <- Conc <$> aliasOf (conc x)
  let lk = M.lookup x' (heapConstr h)
  case lk of
    Nothing -> terr $ "Construction not found: " <> pretty x
    Just c -> return c



addDestr :: Hyp Id -> Destr Id -> TC a -> TC a
addDestr x (Cut c _ct) k = addCut x c k
addDestr x d k = do
  h <- ask
  let d' = getAlias (heapAlias h) <$> d
  report ("Adding destr."
        $$+ pretty x <+> "="
        $$+ pretty d  <+> "; aliased to" <+> pretty d')
  local (addCut' x (Left d')) $ case M.lookup d' (heapRevDestr h) of
     Just y -> addAlias y x k
     Nothing -> local (addDestr' d' x) k

-- | return true if fizzled, otherwise call the continuation.
addConstr :: Monoid a => Conc Id -> Constr' -> TC a -> TC a
addConstr x c k = do
  h <- ask
  let c' = getAlias (heapAlias h) <$> c
  report ("Adding construction"
        $$+ pretty x <+> "="
        $$+ pretty c  <+> "; aliased to" <+> pretty c')
  case c of
    Tag t | Just (Tag t') <- M.lookup x $ heapConstr h ->
         if t /= t' then return mempty else k
    _ -> local (addConstr' x c') $ case M.lookup c' (heapRevConstr h) of
          Just (Conc y) -> addAlias y (conc x) k
          Nothing -> local (addRevConstr' c' x) k

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
  let lk = M.lookup (getAlias (heapAlias h) x) $ heapDestr h
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
  prettier (Pi v x t b) = do
    t' <- pConc t
    b' <- prettier b
    return $ (parens (pretty x <+> (":"<> pretty v) <+> t') <+> "->") $$+ b'
  prettier (Sigma v x t b) = do
    t' <- pConc  t
    b' <- prettier b
    return $ (parens (pretty x <+> (":"<> pretty v) <+> t') <+> " × ") $$+ b'
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
