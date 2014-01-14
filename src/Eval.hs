{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, OverloadedStrings, PatternGuards #-}
module Eval(hnf, onConcl, addTag,unfoldRec) where

import qualified Data.Map as M
import Data.Monoid
import Control.Monad.RWS
import Control.Applicative

import Terms
import Ident
import Display
import TCM
import Heap
import Fresh (freshFrom)

unfoldRec :: Monoid b => Conc Id -> Hyp Id -> Term Id Id -> (Conc Id -> TC b) -> TC b
unfoldRec c r t k = do
  body <- substByDestr r (Cut c (error "rec. typ.")) t
  onConcl body k

hnf :: (Monoid a,r~Id,n~Id) => Conc n -> (Constr n r -> TC a) -> TC a
hnf c k = do
  c' <- lookHeapC c
  case c' of
    (Hyp x) -> hnfHyp x (k (Hyp x)) k  -- Todo: update heap here too?
    _ -> k c'


-- | Look for a redex, and evaluate to head normal form.
hnfHyp :: (Monoid a,r~Id,n~Id) => Hyp n -> TC a -> (Constr n r -> TC a) -> TC a
-- check if there is some reduction to perform. if so replace the thunk by its value in the heap. then this must be a continuation.
hnfHyp x notFound k = enter $ do
  report $ "Evaluating hyp: " <> pretty x
  h <- ask
  let lk = M.lookup (getAlias (heapAlias h) x) $ heapCuts h
  case lk of
    Nothing -> notFound
    Just (Right c) -> do
      report $ "  Is evaluated to concl: " <> pretty c
      hnf c k
    Just (Left d) -> do
      report $ "Evaluating destr: " <> pretty d
      hnfDestr d notFound $ \c -> local (addCut' x $ Right c) (hnf c k)

hnfDestr :: (Monoid a,r~Id,n~Id) => Destr r -> TC a -> (Conc r -> TC a) -> TC a
hnfDestr d notFound k = case d of
   (Proj p f) -> do
          hnfHyp p notFound $ block $ \ (Pair a_ b_) ->
            k $ case f of
               Terms.First -> a_
               Second -> b_
   (App f a_) -> hnfHyp f notFound $ block $ \ (Lam xx bb) -> do
            bb' <- substByDestr xx (Cut a_ (error "body of lambda should not be checked again.")) bb
            onConcl bb' k
   _ -> error $ "cannot be found as target in cut maps: " ++ show d

  where block k' c = case c of
          Hyp _ -> notFound
          _ -> k' c

normalizeAndAddDestr :: Hyp Id -> Destr Id -> TC a -> TC a
normalizeAndAddDestr = addDestr

onConcl :: Monoid a => Term' -> (Conc Id -> TC a) -> TC a
onConcl (Conc c)        k = k c
onConcl (Destr x d t1)  k = normalizeAndAddDestr x d (onConcl t1 k)
onConcl (Constr x c t1) k = addConstr x c (onConcl t1 k)
onConcl (Case x bs)     k = mconcat <$> do
    forM bs $ \(Br tag t1) ->
      addTag x tag $ onConcl t1 k

addTag :: forall a. Monoid a => Hyp Id -> String -> TC a -> TC a
addTag x t k = do
  report $ "Adding tag " <> pretty x <> " = '" <> text t
  hnfHyp x addTag' $ \(Tag t') ->
    if t == t' then k else return mempty  -- conflicting tags, abort.
 where addTag' :: Monoid a => TC a
       addTag' = do
         tName <- liftTC $ freshFrom t
         addConstr tName (Tag t) $  -- todo: don't instroduce a name for an existing tag.
           local (addCut' x $ Right tName) k

