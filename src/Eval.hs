{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, OverloadedStrings, PatternGuards, TypeSynonymInstances, FlexibleInstances #-}
module Eval where

import Data.Bifunctor
import qualified Data.Map as M
import Data.Monoid
import Control.Monad.RWS
import Control.Applicative

import Terms
import Ident
import Display
import TCM
import Fresh (freshFrom)
import Heap

hnf :: (r~Id,n~Id) => Conc n -> (Constr n r -> TC Bool) -> TC Bool
hnf c k = do
  c' <- lookHeapC c
  case c' of
    (Hyp x) -> do
       ts <- heapTags <$> ask
       case M.lookup x ts of
         Just tag -> k (Tag tag) -- Todo: update heap here too?
         Nothing -> hnfHyp x (k (Hyp x)) k  -- Todo: update heap here too?
    _ -> k c'


-- | Look for a redex, and evaluate to head normal form.
hnfHyp :: (r~Id,n~Id) => Hyp n -> TC Bool -> (Constr n r -> TC Bool) -> TC Bool
-- check if there is some reduction to perform. if so replace the thunk by its value in the heap. then this must be a continuation.
hnfHyp x notFound k = do
  tell ["Evaluating hyp: " <> pretty x]
  h <- ask
  let lk = M.lookup (getAlias (heapAlias h) x) $ heapCuts h
  case lk of
    Nothing -> notFound
    Just (Right c) -> do
      tell ["  Is evaluated to concl: " <> pretty c]
      hnf c k
    Just (Left d) -> do
      tell ["Evaluating destr: " <> pretty d]
      hnfDestr d notFound $ \c -> local (addCut' x $ Right c) (hnf c k)

hnfDestr :: (r~Id,n~Id) => Destr r -> TC Bool -> (Conc r -> TC Bool) -> TC Bool
hnfDestr d notFound k = case d of
   (Proj p f) -> do
          hnfHyp p notFound $ block $ \ (Pair a_ b_) ->
            k $ case f of
               Terms.First -> a_
               Second -> b_
   (App f a_) -> hnfHyp f notFound $ block $ \ (Lam xx bb) -> do
            x' <- liftTC $ freshFrom "λ"
            bb' <- substTC xx x' bb
            onConcl (Destr x' (Cut a_ (error "body of lambda should not be checked again.")) bb') k
   _ -> error $ "cannot be found as target in cut maps: " ++ show d

  where block k' c = case c of
          Hyp _ -> notFound
          _ -> k' c

addFin :: Monoid a => Id -> String -> TC a -> TC a
addFin x t k = do
  h <- ask
  case M.lookup x (heapTags h) of
    Just t' | t /= t' -> return mempty -- conflicting tags, abort.
    _ -> local (\h' -> h' {heapTags = M.insert x t (heapTags h')}) k

addDestr :: Hyp Id -> Destr Id -> TC a -> TC a
addDestr x (Cut c _ct) k = local (addCut' x $ Right c) k
addDestr x d k = do
  h <- ask
  let d' = getAlias (heapAlias h) <$> d
  tell ["Adding destr. " <> pretty x <> " = " <> pretty d  <> " ; aliased to " <> pretty d']
  local (addCut' x $ Left d') $ case M.lookup d' (heapDestr h) of
     Just y -> addAlias y x k
     Nothing -> local (addDestr' d' x) k

-- | return true if fizzled, otherwise call the continuation.
addConstr :: Monoid a => Conc Id -> Constr' -> TC a -> TC a
addConstr x c k = do
  tell ["Adding construction " <> pretty x <> " = " <> pretty c]
  hC <- heapConstr <$> ask
  hA <- heapAlias <$> ask
  case c of
    Tag t | Just (Tag t') <- M.lookup x hC -> if t /= t' then return mempty else k
    _ -> local (addConstr' x $ getAlias hA <$> c) k

instance Monoid Bool where
  mempty = True
  mappend = (&&)

onConcl :: Monoid a => Term' -> (Conc Id -> TC a) -> TC a
onConcl (Conc c)        k = k c
onConcl (Destr x d t1)  k = addDestr x d (onConcl t1 k)
onConcl (Constr x c t1) k = addConstr x c (onConcl t1 k)
onConcl (Case x bs)     k = mconcat <$> do
  forM bs $ \(Br tag t1) ->
    addFin x tag $ onConcl t1 k

class Prettier a where
  prettier :: a -> TC Doc

pConc :: Conc Id -> TC Doc
pConc x = prettier =<< lookHeapC x

pHyp :: Hyp Id -> TC Doc
pHyp x = do
  h <- ask
  let ts = heapTags h
  case M.lookup x ts of
     Just tag -> return $ "'" <> text tag
     _ -> do
       let lk = M.lookup (getAlias (heapAlias h) x) $ heapCuts h
       case lk of
         Nothing -> return $ pretty x
         Just (Right c) -> pConc c
         Just (Left d) -> prettier d

instance Prettier Term' where
  prettier (Conc c) = pConc c
  prettier (Destr h d t) = addDestr h d $ prettier t
  prettier (Constr x c t) = addConstr x c $ prettier t
  prettier (Case x bs) = do
    bs' <- mapM prettier bs
    h <- pHyp x
    return $ hang ("case " <> h <> " of") 2 (braces $ sep $ punctuate "." $ bs')

instance Prettier Constr' where
  prettier (Hyp h) = pHyp h
  prettier (Lam x b) = do
    b' <- prettier b
    return $ "\\" <> pretty x <> " -> " <> b'
  prettier (Pi x t b) = do
    t' <- pConc t
    b' <- prettier b
    return $ parens (pretty x <>":"<> t') <> " -> " <> b'
  prettier (Sigma x t b) = do
    t' <- pConc  t
    b' <- prettier b
    return $ parens (pretty x <>":"<> t') <> " × " <> b'
  prettier (Pair a b) = do
    a' <- pConc  a
    b' <- pConc  b
    return $ parens $ a' <> "," <> b'
  prettier x = return $ pretty x


instance Prettier Destr' where
  prettier (App f x) = do
    f' <- pHyp f
    x' <- pConc x
    return $ f' <+> x'
  prettier (Proj x p) = do
    x' <- pHyp x
    return $ x' <> pretty p
  prettier (Cut x t) = do
    x' <- pConc x
    t' <- pConc t
    return $ x' <+> ":" <+> t'


instance Prettier Branch' where
  prettier (Br tag t) = (\x -> "'" <> text tag <> "->" <> x) <$> prettier t

