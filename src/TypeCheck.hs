{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, OverloadedStrings #-}
module TypeCheck where
import Terms
import qualified Data.Map as M

import Control.Monad.Reader
import Control.Monad.Error
import Control.Monad.Writer
import Control.Applicative
import Eval
import Eq
import Fresh
import Ident
import Display
import TCM
import Heap

-- TODO: don't return a boolean.

typeCheck :: Term' -> Term' -> (Either Doc (),[Doc])
typeCheck a t = runTC (max (nextUnique t) (nextUnique a)) emptyHeap chk
  where chk = do tell ["Start"]
                 checkSort t 100000
                 checkTermAgainstTerm a t

addCtx' :: Ord n => n -> Conc r -> Heap n r -> Heap n r
addCtx' x t h@Heap{..} = h{context = M.insert x t context }

addCtx :: Id -> Conc Id -> (TC ()) -> TC ()
addCtx x t k = do
  tell ["Adding hyp " <> pretty x <> ":" <> pretty t]
  local (addCtx' x t) k

-- Infer the type of a destruction and return it as a normal form.
inferDestr :: (n~Id,r~Id) => Destr r -> (Conc r ->  TC ()) -> TC ()
inferDestr (Cut v vt) k = do
  checkConclSort vt 10000
  checkConcl v vt
  k vt
inferDestr (App f a_) k =
  inferHyp f $ \ft ->
  case ft of
    (Pi x t_ u) -> do
       checkConcl a_ t_
       retTyp <- substByDestr x (Cut a_ t_) u
       onConcl retTyp k
    _ -> throwError $ pretty f <> " has not a function type"
inferDestr (Proj p f) k =
  inferHyp p $ \pt ->
  case pt of
    Sigma x t_ u -> do
       case f of
         Terms.First -> k t_
         Terms.Second -> do
           x' <- liftTC $ freshFrom " "
           u' <- substTC x x' u
           addCtx x' t_ $ onConcl (Destr x' (Proj p Terms.First) u') k
           -- TODO: is the substitution needed? can one just give a
           -- definition for x? No: there can be other instances of x.
           -- A cleaner version would be to refresh binders every time
           -- they are loaded from the heap (lookHeapC)
    _ -> throwError $ pretty p <> " has not a pair type"

-- Direct lookup of type in the context
inferHyp :: (n~Id,r~Id) => Hyp r -> (Constr n r -> TC ()) -> TC ()
inferHyp h k = (\c -> hnf c k) =<< inferHyp' h

inferHyp' :: (n~Id,r~Id) => Hyp r -> TC (Conc r)
inferHyp' h = do
  ctx <- context <$> ask
  case M.lookup h ctx of
    Nothing -> terr $ "Panic: " <> pretty h <> " hyp. not found in context."
    Just c -> return c

-- maintains the invariant that every hyp. has an entry in the context.
checkBindings :: (n~Id,r~Id) => Term n r -> (Conc r -> TC ()) -> TC ()
checkBindings (Conc c) k = k c
checkBindings (Constr x c t1) k = do
  -- tell ["constructing" <> pretty x]
  addConstr x c $ do
    -- tell ["constructed" <> pretty x]
    checkBindings t1 k
checkBindings (Destr x d t1) k = inferDestr d $ \dt -> do
  tell ["inferred " <> pretty d <> " to be of type " <> pretty dt]
  addCtx x dt $ addDestr x d $ checkBindings t1 k
checkBindings (Case x bs) k =
  inferHyp x $ \xt ->
  case xt of
    Fin ts -> do
      let ts' = [t | Br t _ <- bs]
      when (ts /= ts') $ terr $ "mismatching tags in case on " <> pretty x
      forM_ bs $ \(Br tag t1) -> addTag x tag $ checkBindings t1 k
    _ -> terr $ pretty x <> " has not a fin. type, but " <> pretty xt

checkTermAgainstTerm :: (n~Id,r~Id) => Term n r -> Term n r -> TC ()
checkTermAgainstTerm e t = checkBindings e $ \c -> checkConAgainstTerm c t

checkConAgainstTerm :: (n~Id,r~Id) => Conc r -> Term n r -> TC ()
checkConAgainstTerm c t = onConcl t $ \t' -> checkConcl c t'

checkConcl :: (n~Id,r~Id) => Conc r -> Conc r -> TC ()
checkConcl v t = do
  tell ["checking conclusion " <> pretty v <> ":" <> pretty t]
  v' <- lookHeapC v
  checkConstrAgainstConcl v' t

checkConstrAgainstConcl :: (n~Id,r~Id) => Constr n r -> Conc r -> TC ()
checkConstrAgainstConcl (Hyp h) u = checkHyp h u
checkConstrAgainstConcl (Rec n b) t = addCtx n t $ checkTermAgainstTerm b (Conc t)
checkConstrAgainstConcl v t = do
  tell ["checking construction"
        $$+ (sep ["val" <+> pretty v, "typ" <+> pretty t])]
  hnf t $ \t' -> checkConstr v t'

checkHyp h u = do
  t <- inferHyp' h
  eq <- testConc t u
  unless eq $ terr $ pretty t <> " not a subtype of " <> pretty u <> " hence the type of " <> pretty h <> " is wrong"

checkConstr :: (n~Id,r~Id) => Constr n r -> Constr n r -> TC ()
checkConstr (Hyp _) t = error "dealt with above"
checkConstr (Pair a_ b_) (Sigma xx ta_ tb_) = do
  checkConcl a_ ta_
  tb' <- substByDestr xx (Cut a_ ta_) tb_
  checkConAgainstTerm b_  tb'
checkConstr (Lam x b_) (Pi xx ta_ tb_) = do
  addCtx x ta_ $ addAlias xx x $ checkTermAgainstTerm b_ tb_
checkConstr tag@(Tag t) ty@(Fin ts) = unless  (t `elem` ts) $ terr $
   pretty tag <> " is not found in " <> pretty ty
checkConstr (Sigma xx ta_ tb_) (Universe s) = do
  checkConclSort ta_ s
  addCtx xx ta_ $ checkSort tb_ s
checkConstr (Pi xx ta_ tb_) (Universe s) = do
  checkConclSort ta_ s
  addCtx xx ta_ $ checkSort tb_ s
checkConstr (Fin _) (Universe _s) = return ()
checkConstr (Universe s') (Universe s) =
  unless (s' < s) $ terr $ int s' <> " is not a subsort of" <> int s

checkConstr v t = terr $ hang "Type mismatch: " 2 $ sep ["value: " <> pretty v, "type: " <> pretty t]

checkSort :: (n~Id,r~Id) => Term n r -> Int -> TC ()
checkSort t s = checkBindings t $ \c -> checkConclSort c s

checkConclSort :: (n~Id,r~Id) => Conc r -> Int -> TC ()
checkConclSort c s = do
  tell ["checking " <> pretty c <> " has sort " <> pretty s]
  s' <- liftTC $ freshFrom $ ("*" ++ subscriptShow s ++ " ")
  addConstr s' (Universe s) $ checkConcl c s' -- TODO: don't allocate duplicate sort names.
