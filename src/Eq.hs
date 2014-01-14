{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, OverloadedStrings, PatternGuards #-}
module Eq (testConstr, testConc) where
import Terms
import qualified Data.Map as M
import Data.Monoid
import Control.Monad.RWS
import Control.Applicative
import Ident
import Display
import TCM
import Heap
import Eval


testTerm :: (r~Id,n~Id) =>   Term n r -> Term n r -> TC Bool
testTerm t1 t2 = onConcl t1 $ \c1 -> onConcl t2 $ \c2 -> testConc c1 c2

testConc :: (r~Id,n~Id) => Conc r -> Conc r -> TC Bool
testConc x_1 x_2
  | x_1 == x_2 = return True -- optimisation, so equal structures are not deeply traversed.
  | otherwise = hnf x_1 $ \c1 -> hnf x_2 $ \c2 -> testConstr' c1 c2

dbgTest msg x y = report $ "Testing " <> msg <> ": " <> pretty x <> " <= " <> pretty y

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
testConstr (Rec r1 t1)(Rec r2 t2) = local (addAlias' r1 r2) $ testTerm t1 t2 -- note that we don't unfold here!
testConstr _ _ = return False

testHyp :: Hyp Id -> Hyp Id -> TC Bool
testHyp a1 a2 = do
  dbgTest "Hyp " a1 a2
  h1 <- aliasOf a1
  h2 <- aliasOf a2
  md1 <- lookDestr h1
  md2 <- lookDestr h2
  if h1 == h2 then return True
              else case (md1,md2) of
     (Just (Left d1), Just (Left d2)) -> testDestr d1 d2
       -- we don't have to care about the 'right' case here: if the
       -- hyp were evaluated, then the hnf reduction would have taken
       -- care of further evaluation before reaching this point.
     _ -> return False

lookDestr x = do
  hC <- heapCuts <$> ask
  return $ M.lookup x hC

testDestr (Proj p1 f1) (Proj p2 f2) = (&&) <$> pure (f1 == f2) <*> testHyp p1 p2
testDestr (App f1 a1) (App f2 a2) = (&&) <$> testHyp f1 f2 <*> testConc a1 a2
testDestr _ _ = return False
