{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, OverloadedStrings, PatternGuards #-}
module Eval(hnf, onConcl, addTag, addSplit, unfoldRec,hnfUnfoldRec) where

import qualified Data.Map as M
import Data.Monoid
import Control.Monad.RWS
import Control.Applicative

import Terms
import Ident
import Display
import TCM
import Heap
import Fresh (refreshId,freshFrom)

unfoldRec :: Monoid b => Conc Id -> Hyp Id -> Term Id Id -> (Conc Id -> TC b) -> TC b
unfoldRec c r t k = do
  body <- substByDestr r (Cut c (error "rec. typ.")) t
  onConcl body k

hnfUnfoldRec :: (Monoid a,r~Id,n~Id) => Conc Id -> (Constr Id Id -> TC a) -> TC a
hnfUnfoldRec c k = do
  hnf c $ \c' -> case c' of
    Rec r t -> unfoldRec c r t $ \c'' -> hnfUnfoldRec c'' k
    _ -> k c'

hnf :: (Monoid a,r~Id,n~Id) => Conc n -> (Constr n r -> TC a) -> TC a
hnf c k = do
  c' <- lookHeapC c
  case c' of
    (Hyp x) -> hnfHyp False x (k (Hyp x)) k  -- Todo: update heap here too?
    _ -> k c'


-- | Look for a redex, and evaluate to head normal form. (no Rec allowed in the result)
hnfHyp :: (Monoid a,r~Id,n~Id) => Bool -> Hyp n -> TC a -> (Constr n r -> TC a) -> TC a
-- check if there is some reduction to perform. if so replace the thunk by its value in the heap. then this must be a continuation.
hnfHyp shouldUnfoldRec x notFound k = enter $ do
  report $ "Evaluating hyp: " <> pretty x
  h <- ask
  let lk = M.lookup (getAlias (heapAlias h) x) $ heapCuts h
  case lk of
    Nothing -> notFound
    Just (Right c) -> do
      report $ "  Is evaluated to concl: " <> pretty c
      locHnf c k
    Just (Left d) -> do
      report $ "Evaluating destr: " <> pretty d
      hnfDestr d notFound $ \c -> addCut x (Right c) (locHnf c k)
 where locHnf = if shouldUnfoldRec then hnfUnfoldRec else hnf

hnfDestr :: (Monoid a,r~Id,n~Id) => Destr r -> TC a -> (Conc r -> TC a) -> TC a
hnfDestr d notFound k = case d of
   (App f a_) -> hnfHyp True f notFound $ block $ \ (Lam xx bb) -> do
            bb' <- substByDestr xx (Cut a_ (error "body of lambda should not be checked again.")) bb
            onConcl bb' k
   _ -> error $ "cannot be found as target in cut maps: " ++ show d

  where block k' c = case c of
          Hyp _ -> notFound
          _ -> k' c

normalizeAndAddDestr :: Hyp Id -> Destr Id -> TC a -> TC a
normalizeAndAddDestr = addDestr

onConcl :: Monoid a => Term' -> (Conc Id -> TC a) -> TC a
onConcl (Concl c)       k = k c
onConcl (Destr x d t1)  k = normalizeAndAddDestr x d (onConcl t1 k)
onConcl (Constr x c t1) k = addConstr x c (onConcl t1 k)
onConcl (Split x y z t1) k = addSplit x y z $ onConcl t1 k
onConcl (Case x bs)     k = mconcat <$> do
    forM bs $ \(Br tag t1) ->
      addTag x tag $ onConcl t1 k

addTag :: forall a. Monoid a => Hyp Id -> String -> TC a -> TC a
addTag x t k = do
  report $ "Adding tag " <> pretty x <> " = '" <> text t
  hnfHyp True x addTag' $ \(Tag t') ->
    if t == t' then k else return mempty  -- conflicting tags, abort.
 where addTag' :: Monoid a => TC a
       addTag' = do
         tName <- Conc <$> do liftTC $ freshFrom t
         addConstr tName (Tag t) $  -- todo: don't instroduce a name for an existing tag.
           addCut x (Right tName) k

addSplit :: (Monoid a,r~Id,n~Id) => Hyp r -> Hyp r -> Hyp n -> TC a -> TC a
addSplit x y z k = do
  hnfHyp True z addSplit' $ \(Pair x' y') ->
    addCut x (Right x') $
      addCut y (Right y') $
        k
  where addSplit' = do
          xName <- Conc <$> liftTC (refreshId x)
          yName <- Conc <$> liftTC (refreshId y)
          zName <- Conc <$> liftTC (refreshId z)
          addConstr xName (Hyp x) $
             addConstr yName (Hyp y) $
             addConstr zName (Pair xName yName) $
               addCut z (Right zName) k


