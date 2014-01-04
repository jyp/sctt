{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, OverloadedStrings #-}
module Eq where
import Terms
import qualified Data.Map as M
import Data.Monoid
import Control.Monad.RWS
import Control.Applicative
import Ident
import Display
import TCM
import Data.Bifunctor

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

addAliases :: [(Id,Id)] -> TC Bool -> TC Bool
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

addAlias :: Id -> Id -> TC Bool -> TC Bool
addAlias src trg = addAliases [(src,trg)]

aliasOf :: Id -> TC Id
aliasOf x = flip getAlias x . heapAlias <$> ask

getEliminated (Proj x _) = x
getEliminated (App x _) = x


-- | Look for some constructed value in the heap.
lookHeapC :: (r~Id,n~Id) => n -> (Constr n r -> TC Bool) -> TC Bool
-- check if there is some reduction to perform. if so replace the thunk by its value in the heap. then this must be a continuation.
lookHeapC x k = do
  lk <- M.lookup x . heapConstr <$> ask
  case lk of
    Nothing -> error "Construction not found"
    Just c -> k c

hnf' :: (r~Id,n~Id) => Conc n -> (Constr n r -> TC Bool) -> TC Bool
hnf' c k = lookHeapC c $ \c' -> case c' of
  (Hyp x) -> hnf x (k (Hyp x)) $ \c'' -> hnf' c'' k
  _ -> k c'

-- | Look for a redex, and evaluate to head normal form.
hnf :: (r~Id,n~Id) => n -> (TC Bool) -> (Conc r -> TC Bool) -> TC Bool
-- check if there is some reduction to perform. if so replace the thunk by its value in the heap. then this must be a continuation.
hnf x notFound k = do
  lk <- M.lookup x . heapCuts <$> ask
  case lk of
    Nothing -> notFound
    Just (Right c) -> k c
    Just (Left d) -> eval1 d $ \d' -> onConcl d' $ \c ->
                   local (addCut' x $ Right c) (k c)

eval1 :: (r~Id,n~Id) => Destr r -> (Term n r -> TC Bool) -> TC Bool
eval1 (Proj p f) k = do
  lookHeapC p $ \(Pair a_ b_) -> k $ Conc $ case f of
    Terms.First -> a_; Second -> b_
eval1 (App f a_) k = lookHeapC f $ \(Lam xx bb) -> do
    k =<< substTC xx a_ bb
eval1 (Cut _ _) k = error "cut cannot be found as target in cut maps"

addDestr :: Hyp Id -> Destr Id -> TC Bool -> TC Bool
addDestr x (Cut c _ct) k = local (addCut' x $ Right c) k
addDestr x d k = do
  h <- ask
  let dHeap = heapDestr h
      aHeap = heapAlias h
      cHeap = heapConstr h
      d' = getAlias aHeap <$> d
      y = getEliminated d
  case M.lookup y cHeap of
    Just _ -> local (addCut' x $ Left d') k
    Nothing -> case M.lookup d' dHeap of
      Just y -> addAlias y x k
      Nothing -> local (addDestr' d' x) k


-- | return true if fizzled, otherwise call the continuation.  
addConstr :: Conc Id -> Constr' -> TC Bool -> TC Bool
addConstr x c k = do
  tell ["Adding construction " <> pretty x <> " = " <> pretty c]
  hC <- heapConstr <$> ask
  hA <- heapAlias <$> ask
  case c of
    Tag t | Just (Tag t') <- M.lookup x hC, t /= t' -> return True
    _ -> local (addConstr' x $ getAlias hA <$> c) k

onConcl :: Term' -> (Conc Id -> TC Bool) -> TC Bool
onConcl (Conc c) k = k c
onConcl (Destr x d t1) k = addDestr x d (onConcl t1 k)
onConcl (Constr x c t1) k = addConstr x c (onConcl t1 k)
onConcl (Case x bs) k = and <$> forM bs (\(Br tag t1) ->
  addConstr x (Tag tag) $ onConcl t1 k)

testTerm :: (r~Id,n~Id) =>   Term n r -> Term n r -> TC Bool
testTerm t1 t2 = onConcl t1 $ \c1 -> onConcl t2 $ \c2 -> testConc c1 c2

testConc :: (r~Id,n~Id) => Conc r -> Conc r -> TC Bool
testConc x_1 x_2
  | x_1 == x_2 = return True -- optimisation, so equal deep structures are not traversed.
  | otherwise = lookHeapC x_1 $ \c1 -> lookHeapC x_2 $ \c2 -> testConstr c1 c2

testConstr :: (r~Id,n~Id) => Constr n r -> Constr n r -> TC Bool
testConstr (Hyp h1) (Hyp h2) = (==) <$> aliasOf h1 <*> aliasOf h2 -- FIXME: evaluation
testConstr (Lam x1 t1) (Lam x2 t2) = local (addAlias' x1 x2) $ testTerm t1 t2
testConstr (Pair a1 b1)(Pair a2 b2) = testConc a1 a2 >> testConc b1 b2
testConstr (Pi x1 a1 t1) (Pi x2 a2 t2) = testConc a2 a1 >> (local (addAlias' x1 x2) $ testTerm t1 t2)
testConstr (Sigma x1 a1 t1) (Sigma x2 a2 t2) = testConc a1 a2 >> (local (addAlias' x1 x2) $ testTerm t1 t2)
testConstr (Tag t1)(Tag t2) = return $ t1 == t2
testConstr (Fin ts1)(Fin ts2) = return $ ts1 == ts2
testConstr (Universe x1)(Universe x2) = return $ x1 <= x2 -- yes, we do subtyping: TODO make that clean in the names
testConstr _ _ = return False

