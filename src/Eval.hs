{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, OverloadedStrings, PatternGuards #-}
module Eval(hnf, onConcl, addTag, addSplit, unfoldRec,hnfUnfoldRec, normalizeAndAddDestr) where

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

-- | Top-level head normalization function.
--
--   Takes a conclusion and looks it up in the heap.
--   If it is bound to a hypothesis, recursively evaluate that by calling @hnfHyp@.
--   Otherwise, it must be a construction, and we are done.
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
  -- lookup definition of hypothesis
  let lk = M.lookup (getAlias (heapAlias h) x) $ heapDestr h
  case lk of
    -- case: abstract (free) hypothesis without a definition
    Nothing -> k (Hyp x)
    -- case: already in head normal form
    Just (Right c) -> do
      report $ "Is evaluated to concl: " <> pretty c
      lookHeapUF unfold c k
    -- case: its a destruction of something, so possibly a redex, need to normalize
    Just (Left d) -> do
      report $ "Evaluating destr: " <> pretty d
      enter $ hnfDestr unfold x d $ \c -> addDef x c (k c)

-- | Normalize a destruction.
hnfDestr :: (Monoid a,r~Id,n~Id) => Bool -> Hyp r -> Destr r -> (Constr n r -> TC a) -> TC a
hnfDestr unfold h d k = case d of
   -- only lazy destruction is application
   (App f a_) -> hnfHyp True f $ \c -> case c of
       -- case: beta-redex
       (Lam xx bb) -> do
            bb' <- substByDestr xx (Cut a_ (error "body of lambda should not be checked again.")) bb
            onConcl bb' $ \c1 -> do
              report $ "Application " <> pretty f <> " " <> pretty a_ <> " reduces to " <> pretty c1
              hnf' unfold c1 k
       -- case: neutral
       Hyp _ -> do
         -- Check whether the application is has an abbreviation (=alias) h'.
         -- This alias could be bound to a definition (see "smart case").
         --
         -- This is necessary because after evaluation of 'f', the
         -- hyp. may have been aliased to another hyp which now has a
         -- definition.
         h' <- aliasOf h
         if h' /= h -- condition to avoid looping
            then hnfHyp unfold h' k  -- to establish unique normal forms wrt. sharing
            else k (Hyp h)
       _ -> error $ "type-error in app-evaluation"
   _ -> error $ "cannot be found as target in cut maps: " ++ show d

