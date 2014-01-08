{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, OverloadedStrings, PatternGuards, TypeSynonymInstances, FlexibleInstances #-}
module Eval where
import Terms
import qualified Data.Map as M
import Data.Monoid
import Control.Monad.RWS
import Control.Applicative
import Ident
import Display
import TCM
import Data.Bifunctor
import Fresh (freshFrom)

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

hnf' :: (r~Id,n~Id) => Conc n -> (Constr n r -> TC Bool) -> TC Bool
hnf' c k = do
  c' <- lookHeapC c
  case c' of
    (Hyp x) -> do
       ts <- heapTags <$> ask
       case M.lookup x ts of
         Just tag -> k (Tag tag)
         Nothing -> hnf x (k (Hyp x)) $ \c'' -> hnf' c'' k
    _ -> k c'

-- | Look for a redex, and evaluate to head normal form.
hnf :: (r~Id,n~Id) => Hyp n -> (TC Bool) -> (Conc r -> TC Bool) -> TC Bool
-- check if there is some reduction to perform. if so replace the thunk by its value in the heap. then this must be a continuation.
hnf x notFound k = do
  tell ["Evaluating hyp: " <> pretty x]
  h <- ask
  let lk = M.lookup (getAlias (heapAlias h) x) $ heapCuts h
  case lk of
    Nothing -> do
      notFound
    Just (Right c) -> do
      tell ["  Is evaluated to concl: " <> pretty c]
      k c
    Just (Left d) -> do
      tell ["Evaluating destr: " <> pretty d]
      eval1 d notFound $ \c ->
         local (addCut' x $ Right c) (k c)

eval1 :: (r~Id,n~Id) => Destr r -> TC Bool -> (Conc r -> TC Bool) -> TC Bool
eval1 (Proj p f) notFound k = do
  hnf p notFound $ \p' -> do
    (Pair a_ b_) <- lookHeapC p'
    k $ case f of
       Terms.First -> a_
       Second -> b_
eval1 (App f a_) notFound k = hnf f notFound $ \f' -> do
    (Lam xx bb) <- lookHeapC f'
    x' <- liftTC $ freshFrom "λ"
    bb' <- substTC xx x' bb
    onConcl (Destr x' (Cut a_ (error "body of lambda should not be checked again.")) bb') k
eval1 d _ _ = error $ "cannot be found as target in cut maps: " ++ show d

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
    Tag t | Just (Tag t') <- M.lookup x hC, t /= t' -> return mempty
    _ -> local (addConstr' x $ getAlias hA <$> c) k

instance Monoid Bool where
  mempty = True
  mappend = (&&)
  
onConcl :: Monoid a => Term' -> (Conc Id -> TC a) -> TC a
onConcl (Conc c) k = k c
onConcl (Destr x d t1) k = addDestr x d (onConcl t1 k)
onConcl (Constr x c t1) k = addConstr x c (onConcl t1 k)
onConcl (Case x bs) k = mconcat <$> forM bs (\(Br tag t1) ->
  addFin x tag $ onConcl t1 k)

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

