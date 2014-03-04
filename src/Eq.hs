{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, OverloadedStrings, PatternGuards #-}
module Eq (isSubTypeOf) where
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
import Fresh (freshId, refreshId)

-- | Direction of the subtyping. Give the "bigger" part.
data Dir = L | E | R

instance Pretty Dir where
    pretty R = "≤"
    pretty E = "="
    pretty L = "≥"

inv L = R
inv E = E
inv R = L

subCompare R = (<=)
subCompare E = (==)
subCompare L = (>=)



x <&&> y = do
  rx <- x
  if rx then y else return False

isSubTypeOf :: (r~Id) => (Variance, Conc r) -> (Variance, Conc r) -> TC Bool
isSubTypeOf (v1,t1) (v2,t2) =
    return (subCompare R v1 v2) <&&> testConc R t1 t2


testTerm :: (r~Id,n~Id) => Dir -> Term n r -> Term n r -> TC Bool
testTerm d t1 t2 = onConcl t1 $ \c1 -> onConcl t2 $ \c2 -> testConc d c1 c2

testConc :: (r~Id,n~Id) => Dir -> Conc r -> Conc r -> TC Bool
testConc d x_1 x_2
  | x_1 == x_2 = return True -- optimisation, so equal structures are not deeply traversed.
  | otherwise = dbgTest "Conc" d x_1 x_2 $ hnf x_1 $ \c1 -> hnf x_2 $ \c2 -> testConstr' d c1 c2

dbgTest msg d x y k = do
  report $ "Testing" <+> msg <+> ":" <+> pretty x <+> pretty d <+> pretty y
  r <- enter k
  report $ "Result =" <+> pretty r
  return r

testConstr' d c1 c2 = dbgTest "Construction" d c1 c2 $ do
  testConstr d c1 c2


testConstr :: (r~Id,n~Id) => Dir -> Constr n r -> Constr n r -> TC Bool
testConstr d (Hyp a1) (Hyp a2) = testHyp d a1 a2
testConstr d (Lam x1 t1) (Lam x2 t2) = local (addAlias' x1 x2) $ testTerm d t1 t2
testConstr d (Pair a1 b1)(Pair a2 b2) = testConc d a1 a2 <&&> testConc d b1 b2
testConstr d (Pi v1 x1 a1 t1) (Pi v2 x2 a2 t2) | subCompare d v1 v2 =
    testConc (inv d) a1 a2 <&&> (local (addAlias' x1 x2) $ testTerm d t1 t2)
testConstr d (Sigma v1 x1 a1 t1) (Sigma v2 x2 a2 t2) | subCompare d v1 v2 =
    testConc E a1 a2 <&&> (local (addAlias' x1 x2) $ testTerm d t1 t2)
    -- The variance here deserve discussion.
testConstr _ (Tag t1)(Tag t2) = return $ t1 == t2
testConstr _ (Fin ts1)(Fin ts2) = return $ ts1 == ts2
testConstr d (Universe x1)(Universe x2) =
    return $ subCompare d x1 x2
testConstr d (Rec r1 t1)(Rec r2 t2) = local (addAlias' r1 r2) $ testTerm d t1 t2 -- note that we don't unfold here!

-- handling eta expansion
testConstr d (Lam x tl) (Hyp y) = etaLam d x tl y
testConstr d (Hyp y) (Lam x tl) = etaLam d x tl y

testConstr d (Pair x1 x2) (Hyp y) = etaPair d x1 x2 y
testConstr d (Hyp y) (Pair x1 x2) = etaPair d x1 x2 y

testConstr _ _ _ = return False

etaLam d x tl y = do
  x' <- Conc <$> liftTC (refreshId x)
  z <- liftTC freshId
  z' <- Conc <$> liftTC (refreshId z)
  local (addConstr' x' (Hyp x)) $
   local (addConstr' z' (Hyp z)) $
    normalizeAndAddDestr z (App y x') $
     testTerm d tl (Concl z')

etaPair d x1 x2 y = do
  z1 <- liftTC freshId
  z1' <- Conc <$> liftTC (refreshId z1)
  z2 <- liftTC freshId
  z2' <- Conc <$> liftTC (refreshId z2)
  local (addConstr' z1' (Hyp z1)) $
   local (addConstr' z2' (Hyp z2)) $
    addSplit z1 z2 y $
   ( testConc d x1 z1' <&&> testConc d x2 z2' )


testHyp :: Dir -> Hyp Id -> Hyp Id -> TC Bool
testHyp d a1 a2 = dbgTest "Hyp" d a1 a2 $ do
  h1 <- aliasOf a1
  h2 <- aliasOf a2
  md1 <- lookDestr h1
  md2 <- lookDestr h2
  if h1 == h2 then return True
              else case (md1,md2) of
     (Just (Left d1), Just (Left d2)) -> dbgTest "App" d d1 d2 $ testDestr d d1 d2
       -- we don't have to care about the 'right' case here: if the
       -- hyp were evaluated, then the hnf reduction would have taken
       -- care of further evaluation before reaching this point.
     _ -> return False

lookDestr x = do
  hC <- heapDestr <$> ask
  return $ M.lookup x hC

testDestr d (App f1 a1) (App f2 a2) = testHyp d f1 f2 <&&> testConc d a1 a2
testDestr _ _ _ = return False
