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

hnf,hnfUnfoldRec :: (Monoid a,r~Id,n~Id) => Conc Id -> (Constr Id Id -> TC a) -> TC a
hnfUnfoldRec = hnf' True
hnf = hnf' False


lookHeapUF :: Monoid a => Bool -> Conc Id -> (Constr Id Id -> TC a) -> TC a
lookHeapUF unfold c k = do
  c' <- lookHeapC c
  case c' of
    Rec r t | unfold -> unfoldRec c r t (\c'' -> lookHeapUF unfold c'' k)
    _ -> k c'

hnf' :: (Monoid a,r~Id,n~Id) => Bool -> Conc n -> (Constr n r -> TC a) -> TC a
hnf' unfold c k = lookHeapUF unfold c $ \c' -> case c' of
    Hyp x -> hnfHyp unfold x k
    _ -> k c'


-- | Look for a redex, and evaluate to head normal form. (no Rec allowed in the result)
hnfHyp :: (Monoid a,r~Id,n~Id) => Bool -> Hyp r -> (Constr n r -> TC a) -> TC a
-- check if there is some reduction to perform. if so replace the thunk by its value in the heap. then this must be a continuation.
hnfHyp unfold x k = do
  report $ "Evaluating hyp: " <> pretty x
  h <- ask
  let lk = M.lookup (getAlias (heapAlias h) x) $ heapCuts h
  case lk of
    Nothing -> k (Hyp x)
    Just (Right c) -> do
      report $ "Is evaluated to concl: " <> pretty c
      lookHeapUF unfold c k
    Just (Left d) -> do
      report $ "Evaluating destr: " <> pretty d
      enter $ hnfDestr unfold x d $ \c -> addDef x c (k c)

hnfDestr :: (Monoid a,r~Id,n~Id) => Bool -> Hyp r -> Destr r -> (Constr n r -> TC a) -> TC a
hnfDestr unfold h d k = case d of
   (App f a_) -> hnfHyp True f $ \c -> case c of
       (Lam xx bb) -> do
            bb' <- substByDestr xx (Cut a_ (error "body of lambda should not be checked again.")) bb
            report $ "Application " <> pretty f <> " " <> pretty a_
            onConcl bb' $ \c1 -> do
              report $ "Reduces to " <> pretty c1
              hnf' unfold c1 k
       Hyp f' -> do
         h' <- liftTC $ refreshId h
         addDestr h' (App f' a_) $ k (Hyp h')
       _ -> error $ "type-error in app-evaluation"
   _ -> error $ "cannot be found as target in cut maps: " ++ show d

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
  hnfHyp True x $ \c -> case c of
    (Tag t') -> if t == t' then k else return mempty  -- conflicting tags, abort.
    (Hyp x') -> do
         tName <- Conc <$> do liftTC $ freshFrom t
         addConstr tName (Tag t) $  -- todo: don't instroduce a name for an existing tag.
           addCut x' (Right tName) k

addSplit :: (Monoid a,r~Id,n~Id) => Hyp r -> Hyp r -> Hyp n -> TC a -> TC a
addSplit x y z k = do
  hnfHyp True z $ \c -> case c of
    Pair x' y' -> addCut x (Right x') $
                   addCut y (Right y') $
                    k
    Hyp z' -> do
          xName <- Conc <$> liftTC (refreshId x)
          yName <- Conc <$> liftTC (refreshId y)
          zName <- Conc <$> liftTC (refreshId z)
          addConstr xName (Hyp x) $
             addConstr yName (Hyp y) $
             addConstr zName (Pair xName yName) $
               addCut z' (Right zName) k


