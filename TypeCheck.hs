{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, OverloadedStrings #-}
module TypeCheck where
import Terms
import qualified Data.Map as M

import Control.Monad.Reader
import Control.Monad.Error
import Control.Monad.Writer
import Control.Applicative
import Eq
import Fresh
import Ident
import Display
import TCM

-- TODO: don't return a boolean.

terr :: Doc -> TC a
terr msg = do
  h <- ask
  throwError $ sep [hang "heap" 2 (pretty h), msg]

checkTyp :: Term' -> (Either Doc Bool,[Doc])
checkTyp t = runTC (nextUnique t) emptyHeap chk
  where chk = do tell ["Start"]
                 checkSort t 100000

typeCheck :: Term' -> Term' -> (Either Doc Bool,[Doc])
typeCheck a t = runTC (max (nextUnique t) (nextUnique a)) emptyHeap chk
  where chk = do tell ["Start"]
                 checkSort t 100000
                 checkTermAgainstTerm a t

addCtx' :: Ord n => n -> Conc r -> Heap n r -> Heap n r
addCtx' x t h@Heap{..} = h{context = M.insert x t context }

addCtx :: Id -> Conc Id -> (TC Bool) -> TC Bool
addCtx x t k = do
  tell ["Adding hyp " <> pretty x <> ":" <> pretty t]
  local (addCtx' x t) k

-- Infer the type of a destruction and return it as a normal form.
inferDestr :: (n~Id,r~Id) => Destr r -> (Conc r ->  TC Bool) -> TC Bool
inferDestr (Cut v vt) k = do
  checkConclSort vt 10000
  checkConcl v vt
  k vt
inferDestr (App f a_) k =
  inferHyp f $ \ft -> 
  case ft of
    (Pi x t_ u) -> do
       checkConcl a_ t_
       retTyp <- substTC x a_ u
       onConcl retTyp k
    _ -> throwError $ pretty f <> " has not a function type"
inferDestr (Proj p f) k =
  inferHyp p $ \pt ->
  case pt of
    (Sigma x t_ u) -> do
       case f of
         Terms.First -> k t_
         Terms.Second -> do
           x' <- liftTC freshId
           u' <- substTC x x' u
           onConcl (Destr x' (Proj p Terms.First) u') k
    _ -> throwError $ pretty p <> " has not a pair type"

-- Direct lookup of type in the context
inferHyp :: (n~Id,r~Id) => Hyp r -> (Constr n r -> TC Bool) -> TC Bool
inferHyp h k = do
  ctx <- context <$> ask
  case M.lookup h ctx of
    Nothing -> terr $ "Panic: " <> pretty h <> " hyp. not found in context."
    Just c -> hnf' c k

-- maintains the invariant that every hyp. has an entry in the context.
checkBindings :: (n~Id,r~Id) => Term n r -> (Conc r -> TC Bool) -> TC Bool
checkBindings (Conc c) k = k c
checkBindings (Constr x c t1) k = do
  -- tell ["constructing" <> pretty x]
  addConstr x c $ do
    -- tell ["constructed" <> pretty x]
    checkBindings t1 k
checkBindings (Destr x d t1) k = inferDestr d $ \dt -> do
  tell ["inferred " <> pretty d <> " to be " <> pretty dt]
  addCtx x dt $ addDestr x d $ checkBindings t1 k
checkBindings (Case x bs) k =
  inferHyp x $ \xt ->
  case xt of
    Fin ts -> do
      rs <- forM bs $ \(Br tag t1) -> do
        when (tag `notElem` ts) $ throwError $ "type error in case on " <> pretty x <> ": " <> text tag <> " not in " <> pretty xt
        addFin x tag $ checkBindings t1 k
      return $ and rs
    _ -> terr $ pretty x <> " has not a fin. type, but " <> pretty xt

checkTermAgainstTerm :: (n~Id,r~Id) => Term n r -> Term n r -> TC Bool
checkTermAgainstTerm e t = checkBindings e $ \c -> checkConAgainstTerm c t

checkConAgainstTerm :: (n~Id,r~Id) => Conc r -> Term n r -> TC Bool
checkConAgainstTerm c t = onConcl t $ \t' -> checkConcl c t'

checkConcl :: (n~Id,r~Id) => Conc r -> r -> TC Bool
checkConcl v t = do
  tell ["checking conclusion " <> pretty v <> ":" <> pretty t]
  hnf' t $ \t' -> checkConclAgainstConstr v t'

checkConclAgainstConstr :: (n~Id,r~Id) => Conc r -> Constr n r -> TC Bool
checkConclAgainstConstr v t = lookHeapC v $ \v' -> do
  tell [hang "checking construction " 2 (sep ["val " <> pretty v', "typ " <> pretty t])]
  checkConstr v' t

checkConstr :: (n~Id,r~Id) => Constr n r -> Constr n r -> TC Bool
checkConstr (Hyp h) t = inferHyp h $ \t' -> do
  v <- testConstr t' t
  when (not v) $ terr $ pretty t <> " not a subtype of " <> pretty t'
  return True
checkConstr (Pair a_ b_) (Sigma xx ta_ tb_) = do
  checkConcl a_ ta_
  checkConAgainstTerm b_ =<< substTC xx a_ tb_
checkConstr (Lam x b_) (Pi xx ta_ tb_) = do
  addCtx x ta_ $ addAlias xx x $ checkTermAgainstTerm b_ tb_
checkConstr (Tag t) (Fin ts) = return (t `elem` ts)
checkConstr (Sigma xx ta_ tb_) (Universe s) = do
  checkConclSort ta_ s
  addCtx xx ta_ $ checkSort tb_ s
checkConstr (Pi xx ta_ tb_) (Universe s) = do
  checkConclSort ta_ s
  addCtx xx ta_ $ checkSort tb_ s
checkConstr (Fin _) (Universe s) = return True
checkConstr (Universe s') (Universe s)
  | s' < s = return True
  | otherwise = terr $ int s' <> " is not a subsort of" <> int s

checkConstr v t = terr $ hang "Type mismatch: " 2 $ sep ["value: " <> pretty v, "type: " <> pretty t]

checkSort :: (n~Id,r~Id) => Term n r -> Int -> TC Bool
checkSort t s = checkBindings t $ \c -> checkConclSort c s

checkConclSort c s = do
  tell ["checking " <> pretty c <> " has sort " <> pretty s]
  hnf' c $ \c' -> checkConstr c' (Universe s)

