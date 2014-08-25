{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, OverloadedStrings #-}
module TypeCheck (typeCheck) where
import Terms
import qualified Data.Map as M

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Applicative
import Fresh
import Ident
import Display
import TCM
import Heap

typeCheck :: Term' -> Term' -> (Either Doc (),[Doc])
typeCheck a t = runTC (max (nextUnique t) (nextUnique a)) emptyHeap chk
  where chk = do report $ "Start"
                 checkBindings t $ \t' -> do
                   checkSort t' 100000
                   checkTerm a t'

addCtx' :: Hyp Id -> Conc Id -> Heap' -> Heap'
addCtx' x ( t) h@Heap{..} = h{context = M.insert x t context }

addCtx :: Id -> Conc Id -> (TC ()) -> TC ()
addCtx x t k = do
  report $ "Adding hyp " <> pretty x <> ":" <> pretty t
  local (addCtx' x t) k

-- Infer the type of a destruction and return it as a normal form.
inferDestr :: (n~Id,r~Id) => Destr r -> (Conc r ->  TC ()) -> TC ()
inferDestr (Cut v vt) k = do
  checkSort vt 10000
  checkVar v vt
  k vt
inferDestr (App f a_) k = do
  ft <- inferHyp f
  case ft of
    (VPi t_ u) -> do
       checkVar a_ t_
       apply u a_ $ \r -> k ( r)
    _ -> terr $ pretty f <> " has not a function type"

-- | Mere lookup of type in the context
inferHyp :: (n~Id,r~Id) => Hyp r -> TC (Val n r)
inferHyp h = do
  ctx <- context <$> ask
  case M.lookup h ctx of
    Nothing -> terr $ "Panic: " <> pretty h <> " hyp. not found in context."
    Just c -> do
      c' <- lookHeap c
      case c' of
        Nothing -> terr $ "Panic: " <> pretty h <> " has an abstract type; so I cannot match it against a construction."
        Just v -> return v

apply :: Id -> Id -> (Id -> TC ()) -> TC ()
apply f a k = do
  x <- liftTC freshId
  addDef x (VApp f a) $ k x
  
-- maintains the invariant that every hyp. has an entry in the context.
checkBindings :: (n~Id,r~Id) => Term n r -> (Conc r -> TC ()) -> TC ()
checkBindings (Concl c) k = k c
checkBindings (Constr ( x) c t1) k = do
  -- report $ "constructing" <> pretty x
  addConstr x c $ do
    -- report $ "constructed" <> pretty x
    checkBindings t1 k
checkBindings (Destr x d t1) k = inferDestr d $ \dt -> do
  report $ "inferred " <> pretty d <> " to be of type " <> pretty dt
  addCtx x dt $ addDestr x d $ checkBindings t1 k
checkBindings (Split x y z t1) k = do
  zt <- inferHyp z
  case zt of
    VSigma t_ u ->
      addCtx x ( t_) $ apply u x $ \u' -> addCtx y ( u') $ addSplit x y z $ checkBindings t1 k
    _ -> do
      doc_z <- pHyp z -- fixme: print the type
      terr $ (pretty z <+> "has not a pair type.") $$+ (pretty zt <+> "=" $$+ doc_z)
checkBindings (Case x bs) k = do
  xt <- inferHyp x
  case xt of
    VFin ts -> do
      let ts' = [t | Br t _ <- bs]
      when (ts /= ts') $ terr $ "mismatching tags in case on " <> pretty x
      forM_ bs $ \(Br tag t1) -> addTag x tag $ checkBindings t1 k
    _ -> terr $ pretty x <> " has not a fin. type, but " <> pretty xt

checkTerm :: (n~Id,r~Id) => Term n r -> n -> TC ()
checkTerm e t = do
  report $ "checking term " <> pretty e <> ":" <> pretty t
  checkBindings e $ \c -> checkVar c t

checkVar :: (n~Id,r~Id) => Conc r -> Conc r -> TC ()
checkVar v t = do
  report $ "checking conclusion " <> pretty v <> ":" <> pretty t
  checkConAgainstVal v =<< lookHeapC t

checkConAgainstVal :: Hyp Id -> Val Id Id -> TC ()
checkConAgainstVal v t' = do
  ctx <- context <$> ask
  case M.lookup v ctx of
    Just _ -> checkHyp v t'
    Nothing -> do
      v' <- lookHeapC v
      report $ "checking construction"
         $$+ (sep ["val" <+> pretty v, "typ" <+> pretty t'])
      checkConstr v' t'

checkConstr :: (n~Id,r~Id) => Val n r -> Val n r -> TC ()
checkConstr (VPair a_ b_) (VSigma ta_ tb_) = do
  checkVar a_ ta_
  apply tb_ a_ $ \tb' -> checkVar b_  tb'
checkConstr (VLam x b_) (VPi ta_ tb_) = do
  addCtx x ta_ $ apply tb_ x $ checkTerm b_
checkConstr tag@(VTag t) ty@(VFin ts) = unless  (t `elem` ts) $ terr $
   pretty tag <> " is not found in " <> pretty ty
checkConstr (VSigma ta_ tb_) (VUniv s) = getSort s $ \ s' -> do
  checkSort ta_ s
  checkConAgainstVal tb_ (VPi ta_ s')
checkConstr (VPi ta_ tb_) (VUniv s) = getSort s $ \ s' -> do
  checkSort ta_ s
  checkConAgainstVal tb_ (VPi ta_ s')
checkConstr (VFin _) (VUniv _s) = return ()
checkConstr (VUniv s') (VUniv s) =
  unless (s' < s) $ terr $ int s' <> " is not a subsort of " <> int s
-- checkConstr x (Rec r t) = do
--   unfoldRec typ r t $ \t' -> checkConstrAgainstConcl x t'
checkConstr (VClosure _ _) _ = error "Closure is not a construction"
checkConstr (VApp _ _) _ = error "App is not a construction"
checkConstr v t = terr $ hang "Type mismatch: " 2 $ sep ["value: " <> pretty v, "type: " <> pretty t]


checkHyp :: Hyp Id -> Val Id Id -> TC ()
checkHyp h u = do
  report $ "checking hypothesis " <> pretty h <> ":" <> pretty u
  t <- inferHyp h
  let eq = t == u
  -- doc_t <- pConc t
  -- doc_u <- pConc u
  doc_h <- pHyp h
  unless eq $ terr $
    pretty t <+> "is not a subtype of" <+> pretty u <+> " in the following context, hence the type of" <+> pretty h <+> "is wrong."
               -- $+$ (pretty t <+> "=") $$+ doc_t
               -- $+$ (pretty u <+> "=") $$+ doc_u
               $+$ (pretty h <+> "=") $$+ doc_h

checkSort :: (n~Id,r~Id) => Conc r -> Int -> TC ()
checkSort c s = do
  report $ "checking " <> pretty c <> " has sort " <> pretty s
  checkConAgainstVal c (VUniv s)

getSort :: Int -> (Id -> TC ()) -> TC ()
getSort s k = do
  x <- liftTC freshId
  addDef x (VUniv s) $ k x
