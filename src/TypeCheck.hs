{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, OverloadedStrings #-}
module TypeCheck (typeCheck) where
import Terms
import qualified Data.Map as M

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Applicative
import Eval
import Eq
import Fresh
import Ident
import Display
import TCM
import Heap

getVar x = do
  ctx <- context <$> ask
  case M.lookup x ctx of
    Nothing -> terr $ "Panic: " <> pretty x <> " hyp. not found in context."
    Just c -> return $ fst c


-- TODO: don't return a boolean.

typeCheck :: Term' -> Term' -> (Either Doc (),[Doc])
typeCheck a t = runTC (max (nextUnique t) (nextUnique a)) emptyHeap chk
  where chk = do report $ "Start"
                 checkSort t 100000
                 checkTermAgainstTerm a (Invar, t)

addCtx' :: Ord n => n -> (Variance, Conc r) -> Heap n r -> Heap n r
addCtx' x t h@Heap{..} = h{context = M.insert x t context }

addCtx :: Id -> (Variance, Conc Id) -> (TC ()) -> TC ()
addCtx x t k = do
  report $ "Adding hyp " <> pretty x <> ":" <> pretty t
  local (addCtx' x t) k

-- Infer the type of a destruction and return it as a normal form.
inferDestr :: (n~Id,r~Id) => Destr r -> (Conc r ->  TC ()) -> TC ()
inferDestr (Cut v vt) k = do
  checkConclSort vt 10000
  checkConcl v (Invar, vt) -- TODO | Not sure if it's the good solution.
  k vt
inferDestr (App f a_) k =
  inferHyp f $ \ft ->
  case ft of
    (Pi v x t_ u) -> do
       checkConcl a_ (v, t_)
       retTyp <- substByDestr x (Cut a_ t_) u
       onConcl retTyp k
    _ -> terr $ pretty f <> " has not a function type"

inferHyp :: (n~Id,r~Id) => Hyp r -> (Constr n r -> TC ()) -> TC ()
inferHyp h k = (\(_,c) -> hnfUnfoldRec c k) =<< inferHyp' h

-- | Mere lookup of type in the context
inferHyp' :: (n~Id,r~Id) => Hyp r -> TC (Variance, Conc r)
inferHyp' h = do
  ctx <- context <$> ask
  case M.lookup h ctx of
    Nothing -> terr $ "Panic: " <> pretty h <> " hyp. not found in context."
    Just c -> return c

-- maintains the invariant that every hyp. has an entry in the context.
checkBindings :: (n~Id,r~Id) => Term n r -> (Conc r -> TC ()) -> TC ()
checkBindings (Concl c) k = k c
checkBindings (Constr x c t1) k = do
  -- report $ "constructing" <> pretty x
  addConstr x c $ do
    -- report $ "constructed" <> pretty x
    checkBindings t1 k
checkBindings (Destr x d t1) k = inferDestr d $ \dt -> do
  report $ "inferred " <> pretty d <> " to be of type " <> pretty dt
  addCtx x (Invar, dt) $ addDestr x d $ checkBindings t1 k
  -- TODO | Compute the correct variance.

checkBindings (Split x y z t1) k = inferHyp z $ \zt -> case zt of
    Sigma v xx t_ u -> do
      u' <- substTC xx x u
      addCtx x (v,t_) $ onConcl u' $ \u'' ->
          addCtx y (Invar, u'') $ addSplit x y z $ checkBindings t1 k
          -- TODO | Compute the correct variance.
    _ -> do
      doc_z <- pHyp z -- fixme: print the type
      terr $ (pretty z <+> "has not a pair type.") $$+ (pretty zt <+> "=" $$+ doc_z)
checkBindings (Case x bs) k =
  inferHyp x $ \xt ->
  case xt of
    Fin ts -> do
      let ts' = [t | Br t _ <- bs]
      when (ts /= ts') $ terr $ "mismatching tags in case on " <> pretty x
      forM_ bs $ \(Br tag t1) -> addTag x tag $ checkBindings t1 k
    _ -> terr $ pretty x <> " has not a fin. type, but " <> pretty xt

checkTermAgainstTerm :: (n~Id,r~Id) => Term n r -> (Variance, Term n r) -> TC ()
checkTermAgainstTerm e t = checkBindings e $ \c -> checkConAgainstTerm c t

checkConAgainstTerm :: (n~Id,r~Id) => Conc r -> (Variance, Term n r) -> TC ()
checkConAgainstTerm c (v,t) = onConcl t $ \t' -> checkConcl c (v, t')

checkConcl :: (n~Id,r~Id) => Conc r -> (Variance, Conc r) -> TC ()
checkConcl v t = do
  report $ "checking conclusion " <> pretty v <> ":" <> pretty t
  v' <- lookHeapC v
  checkConstrAgainstConcl v' t

checkConstrAgainstConcl :: (n~Id,r~Id) => Constr n r -> (Variance, Conc r) -> TC ()
checkConstrAgainstConcl (Hyp h) u = checkHyp h u
checkConstrAgainstConcl (Rec n b) t = do
  addCtx n t $ checkTermAgainstTerm b (fst t, Concl $ snd t)
checkConstrAgainstConcl val (v, typ) = do
  report $ "checking construction"
        $$+ (sep ["val" <+> pretty val, "typ" <+> pretty typ])
  hnf typ $ \typ' -> checkConstr val (v, typ')
    where
        checkConstr :: (n~Id,r~Id) => Constr n r -> (Variance, Constr n r) -> TC ()
        checkConstr (Hyp _) t = error "dealt with above"
        checkConstr (Pair a_ b_) (var, Sigma v xx ta_ tb_) = do
          checkConcl a_ (v, ta_)
          tb' <- substByDestr xx (Cut a_ ta_) tb_
          checkConAgainstTerm b_ (var, tb')
        checkConstr (Lam x b_) (var, Pi v xx ta_ tb_) = do
          addCtx x (v,ta_) $ addAlias xx x $ checkTermAgainstTerm b_ (var, tb_)
        checkConstr tag@(Tag t) ty@(_, Fin ts) = unless  (t `elem` ts) $ terr $
           pretty tag <> " is not found in " <> pretty ty
        checkConstr (Sigma v xx ta_ tb_) (_, Universe s) = do
          checkConclSort ta_ s
          addCtx xx (v, ta_) $ checkSort tb_ s
        checkConstr (Pi v xx ta_ tb_) (_, Universe s) = do
          checkConclSort ta_ s
          addCtx xx (v, ta_) $ checkSort tb_ s
        checkConstr (Fin _) (_, Universe _s) = return ()
        checkConstr (Universe s') (_, Universe s) =
          unless (s' < s) $ terr $ int s' <> " is not a subsort of" <> int s
        checkConstr x (var, Rec r t) = do
          unfoldRec typ r t $ \t' -> checkConstrAgainstConcl x (var, t')

        checkConstr v t = terr $ hang "Type mismatch: " 2 $ sep ["value: " <> pretty v, "type: " <> pretty t]


checkHyp h u = do
  t <- inferHyp' h
  eq <- isSubTypeOf t u
  doc_t <- pConc $ snd t
  doc_u <- pConc $ snd u
  doc_h <- pHyp h
  unless eq $ terr $
    pretty t <+> "is not a subtype of" <+> pretty u <+> " in the following context, hence the type of" <+> pretty h <+> "is wrong."
               $+$ (pretty t <+> "=") $$+ doc_t
               $+$ (pretty u <+> "=") $$+ doc_u
               $+$ (pretty h <+> "=") $$+ doc_h


checkSort :: (n~Id,r~Id) => Term n r -> Int -> TC ()
checkSort t s = checkBindings t $ \c -> checkConclSort c s

checkConclSort :: (n~Id,r~Id) => Conc r -> Int -> TC ()
checkConclSort c s = do
  report $ "checking " <> pretty c <> " has sort " <> pretty s
  s' <- Conc <$> do liftTC $ freshFrom $ ("*" ++ subscriptShow s ++ " ")
  addConstr s' (Universe s) $
   checkConcl c (Invar, s') -- TODO: don't allocate duplicate sort names.
