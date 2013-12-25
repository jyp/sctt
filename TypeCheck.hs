{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables #-}
module Eq where
import Terms
import qualified Data.Map as M

import Control.Monad.Reader
import Control.Applicative

{-type H = Int

data Result a = Success | Cont [(H,a)] | Fail String

newtype TC a = TC {fromTC :: H -> Result a}

instance Monad TC where
  return x = TC (\h -> Cont [(H,a)])
  TC f >>= g = TC $ \h0 -> case f h0 of
    Success -> Success
    Fail s  -> Fail s
    Cont xs -> [ fromTC g a h1 | (h1,a) <- xs] 
-}  

  
-- Infer the type of a destruction and return it as a normal form.
inferDestr :: Destr r -> M n r (Conc r)
inferDestr (Cut v vt) = do
  checkConstr v vt
  return vt
inferDestr (App f a_) = do
  ft <- inferHyp f
  case ft of
    (Pi x t_ u) -> do
       checkConc a_ t_
       retTyp <- subst x a_ u
       whnf retTyp return
inferDestr (Proj p f) = do
  pt <- inferHyp p
  case pt of
    (Sigma x t_ u) -> do
       case p of
         First -> return t_
         Second -> do
           whnf (Let x' (Proj First f) (subst x x' u)) return

-- Direct lookup of type in the context
inferHyp :: Hyp r -> M n r (Constr n r)

checkBindings :: (n ~ r, Ord r) => Term n r -> (Conc r -> M n r Bool) -> M n r Bool
checkBindings (Conc c) k = k c
checkBindings (Constr x c t1) k = addConstr x c (checkBindings t1 k) -- FIXME: check lambdas?!
checkBindings (Destr x d t1) k = do
  -- maintain the invariant that every hyp. has an entry in the context.
  dt <- inferDestr d
  addCtx x dt $ addCut x v $ checkBindings t1 k
checkBindings (Case x bs) k = do
  xt <- inferHyp x
  case xt of
    Fin ts -> do
      rs <- forM bs $ \(Br tag t1) -> do
        when (t1 `notElem` ts) $ error "type error in case"
        addConstr x (Tag tag) $ checkBindings t1 k
        return $ and rs

checkTermAgainstTerm :: Term n r -> Term n r -> M n r ()
checkTermAgainstTerm e t = checkBindings e $ \c -> checkConAgainstTerm t

checkConAgainstTerm :: Concl n r -> Term n r -> M n r ()
checkConAgainstTerm c t = whnf t $ \t' -> checkConAgainstCon t t'

checkConAgainstCon :: Constr n r -> Constr n r -> M n r ()

