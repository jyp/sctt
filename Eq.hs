{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, OverloadedStrings, PatternGuards #-}
module Eq where
import Terms
import qualified Data.Map as M
import Data.Monoid
import Control.Monad.RWS
import Control.Applicative
import Ident
import Display
import TCM
import Data.Maybe (isJust)
import Eval

testTerm :: (r~Id,n~Id) =>   Term n r -> Term n r -> TC Bool
testTerm t1 t2 = onConcl t1 $ \c1 -> onConcl t2 $ \c2 -> testConc c1 c2

testConc :: (r~Id,n~Id) => Conc r -> Conc r -> TC Bool
testConc x_1 x_2
  | x_1 == x_2 = return True -- optimisation, so equal structures are not deeply traversed.
  | otherwise = hnf x_1 $ \c1 -> hnf x_2 $ \c2 -> testConstr' c1 c2

dbgTest msg x y = tell ["Testing " <> msg <> ": " <> pretty x <> " <= " <> pretty y]

testConstr' c1 c2 = do
  dbgTest "Construction " c1 c2
  testConstr c1 c2

testConstr :: (r~Id,n~Id) => Constr n r -> Constr n r -> TC Bool
testConstr (Hyp a1) (Hyp a2) = testHyp a1 a2
testConstr (Lam x1 t1) (Lam x2 t2) = local (addAlias' x1 x2) $ testTerm t1 t2
testConstr (Pair a1 b1)(Pair a2 b2) = testConc a1 a2 >> testConc b1 b2
testConstr (Pi x1 a1 t1) (Pi x2 a2 t2) = testConc a2 a1 >> (local (addAlias' x1 x2) $ testTerm t1 t2)
testConstr (Sigma x1 a1 t1) (Sigma x2 a2 t2) = testConc a1 a2 >> (local (addAlias' x1 x2) $ testTerm t1 t2)
testConstr (Tag t1)(Tag t2) = return $ t1 == t2
testConstr (Fin ts1)(Fin ts2) = return $ ts1 == ts2
testConstr (Universe x1)(Universe x2) = return $ x1 <= x2 -- yes, we do subtyping: TODO make that clean in the names
testConstr _ _ = return False
testHyp a1 a2 = do
  dbgTest "Hyp " a1 a2
  h1 <- aliasOf a1
  h2 <- aliasOf a2
  d1 <- lookDestr h1
  d2 <- lookDestr h2
  or <$> sequence
     [pure $ h1 == h2,
      pure $ isJust d1 && isJust d2 && d1 == d2,
      testApps d1 d2]

lookDestr x = do
  hC <- heapCuts <$> ask
  return $ M.lookup x hC

testApps (Just (Left (App f1 a1))) (Just (Left (App f2 a2))) = (f1 == f2 &&) <$> testConc a1 a2
testApps _ _ = return False
