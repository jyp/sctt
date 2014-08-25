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
                   checkType t'
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
  checkType vt
  checkVar v vt
  k vt
inferDestr (App f a_) k = do
  ft <- inferHyp f
  case ft of
    (VQ Pi t_ u) -> do
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
  
-- maintains the invariant that every hyp. and type has an entry in the context.
checkBindings :: (n~Id,r~Id) => Term n r -> (Conc r -> TC ()) -> TC ()
checkBindings (Concl c) k = k c
checkBindings (Constr y c@(Q _ x t u) t1) k = do
  checkType t
  addCtx x t $ checkBindings u $ \u' -> checkType u'
  addConstr y c $ checkBindings t1 k
  -- OPT: add y to the context.
checkBindings (Constr x c t1) k = do
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
    VQ Sigma t_ u ->
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
checkVar v0 t = do
  ctx <- context <$> ask
  v <- aliasOf v0
  report $ "checking conclusion " <> pretty v <> ":" <> pretty t
  case M.lookup v ctx of
    Just u -> do
      let eq = t == u
      doc_t <- pHyp t
      doc_u <- pHyp u
      doc_h <- pHyp v
      unless eq $ terr $
        pretty t <+> "is not a subtype of" <+> pretty u <+> " in the following context, hence the type of" <+> pretty v <+> "is wrong."
                   $+$ (pretty t <+> "=") $$+ doc_t
                   $+$ (pretty u <+> "=") $$+ doc_u
                   $+$ (pretty v <+> "=") $$+ doc_h
    Nothing -> checkConstr0 v t

isClosure v = case v of
  VClosure _ x -> True
  _ -> False

hnf :: Id -> (Val' -> TC ()) -> TC ()
hnf v k = do
  c <- lookHeap v
  case c of
    Just c' -> k c'
    Nothing -> do
      cl <- lkHeap isClosure v
      case cl of
        Just (VClosure _ t) -> onConcl t $ \v' -> hnf v' k
        Nothing -> terr "cannot be evaluated to head normal form"
      
checkConstr0 :: Id -> Id -> TC ()
checkConstr0 v t = do
  Just v' <- lookHeap v -- cannot fail: things not in the context must be constructions.
  hnf t $ \t' -> do
      report $ "checking construction"
         $$+ (sep ["val" <+> pretty v, "typ" <+> pretty t'])
      checkConstr v' t'

checkConstr :: (n~Id,r~Id) => Val n r -> Val n r -> TC ()
checkConstr (VPair a_ b_) (VQ Sigma ta_ tb_) = do
  checkVar a_ ta_
  apply tb_ a_ $ \tb' -> checkVar b_  tb'
checkConstr (VLam x b_) (VQ Pi ta_ tb_) = do
  addCtx x ta_ $ apply tb_ x $ checkTerm b_
checkConstr tag@(VTag t) ty@(VFin ts) = unless  (t `elem` ts) $ terr $
   pretty tag <> " is not found in " <> pretty ty
checkConstr (VQ _ _ _) (VUniv) = return ()
checkConstr (VFin _) (VUniv) = return ()
checkConstr (VUniv) (VUniv) = return ()
  -- unless (s' < s) $ terr $ int s' <> " is not a subsort of " <> int s
-- checkConstr x (Rec r t) = do
--   unfoldRec typ r t $ \t' -> checkConstrAgainstConcl x t'
checkConstr (VClosure _ _) _ = error "Closure is not a construction"
checkConstr (VApp _ _) _ = error "App is not a construction"
checkConstr v t = terr $ hang "Type mismatch: " 2 $ sep ["value: " <> pretty v, "type: " <> pretty t]



checkType :: (n~Id,r~Id) => Conc r -> TC ()
checkType c = do
  report $ "checking " <> pretty c <> " is a type "
  s <- liftTC freshId
  addDef s VUniv $ do
    s' <- aliasOf s
    checkVar c s'

