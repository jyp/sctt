{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables #-}
module Eq where
import Terms
import qualified Data.Map as M

import Control.Monad.Reader
import Control.Applicative

newtype M n r a = M {runM :: Reader (Heap n r) a}
  deriving (Functor, Applicative, Monad, MonadReader (Heap n r))

run h0 x = runReader (runM x) h0

addAlias' :: Ord r => r -> r -> Heap n r -> Heap n r
addAlias' src trg h@Heap{..} = h{heapAlias = f <$> M.insert src trg heapAlias }
  where f x = if x == src then trg else x

addAliases' :: Ord r => [(r,r)] -> Heap n r -> Heap n r
addAliases' = foldr (.) id . map (uncurry addAlias')

addConstr' :: Ord n => n -> Constr n r -> Heap n r -> Heap n r
addConstr' src trg h@Heap{..} = h{heapConstr = M.insert src trg heapConstr }

addDestr' :: Ord r => Destr r -> n -> Heap n r -> Heap n r
addDestr' src trg h@Heap{..} = h{heapDestr = M.insert src trg heapDestr }


getAlias h x = M.findWithDefault x x h


addAliases :: forall n r. (n~r,Ord r) => [(r,r)] -> M n r Bool -> M n r Bool
addAliases [] k = k
addAliases as k = do
  h <- addAliases' as <$> ask
  let hD' :: M.Map (Destr r) [Hyp n]
      hD' = M.mapKeysWith (++) (fmap (getAlias $ heapAlias h)) $ fmap (:[]) $ heapDestr h
      myhead (x:_) = x
      hD'' = fmap myhead hD'
      classes = M.elems hD'
      aliases = [(x,y) | (x:xs) <- classes, y <- xs]
  local (\h -> h {heapDestr = hD''}) $
    addAliases aliases k

addAlias :: (n~r,Ord r) => r -> r -> M n r Bool -> M n r Bool
addAlias src trg = addAliases [(src,trg)]

aliasOf :: Ord r => r -> M n r r
aliasOf x = flip getAlias x . heapAlias <$> ask

lookHeapC :: Ord n => n -> M n r (Constr n r)
lookHeapC x = do
  cHeap <- asks heapConstr
  case M.lookup x cHeap of
    Just c -> return c

-- | return true if fizzled, otherwise call the continuation.
addDestr :: (n ~ r, Ord r) =>  Hyp n -> Destr r -> M n r Bool -> M n r Bool
addDestr x (Cut c) k = error "cuts not supported yet"
addDestr x d k = do
  dHeap <- asks heapDestr
  case M.lookup d dHeap of
    Just y -> addAlias y x k
    Nothing -> local (addDestr' d x) k


-- | return true if fizzled, otherwise call the continuation.  for now
-- we assume normal forms so adding a construction should never
-- trigger any reduction. Otherwise we need to look for all
-- elimination of the variable and proceed.
addConstr :: Ord n => Conc n -> Constr n r -> M n r Bool -> M n r Bool
addConstr x c k = do
  hC <- heapConstr <$> ask
  case c of
    Tag t | Just (Tag t') <- M.lookup x hC, t /= t' -> return True
    _ -> local (addConstr' x c) k

(<&>) :: Applicative a => a Bool -> a Bool -> a Bool
x <&> y = (&&) <$> x <*> y


testTerm :: (n ~ r, Ord r) =>  Term n r -> Term n r -> M n r Bool
testTerm (Conc c1) (Conc c2) = testConc c1 c2 
testTerm (Destr x d t1) t2 = addDestr x d (testTerm t1 t2)
testTerm (Constr x c t1) t2 = addConstr x c (testTerm t1 t2)
testTerm (Case x bs) t2 = and <$> forM bs (\(Br tag t1) ->
  addConstr x (Tag tag) $ testTerm t1 t2)
testTerm c1 c2 = testTerm c2 c1

testConc :: (n ~ r, Ord r) => Conc r -> Conc r -> M n r Bool
testConc x_1 x_2 = do
  c1 <- lookHeapC =<< aliasOf x_1
  c2 <- lookHeapC =<< aliasOf x_2
  testConstr c1 c2

testConstr :: (n ~ r, Ord r) => Constr n r -> Constr n r -> M n r Bool
testConstr (Hyp h1) (Hyp h2) = (==) <$> aliasOf h1 <*> aliasOf h2
-- testConstr (Alias' c1) c2 = testConstr c2 =<< lookHeapC c1
-- testConstr c1 (Alias' c2) = testConstr c1 =<< lookHeapC c2
testConstr (Lam x1 t1) (Lam x2 t2) = local (addAlias' x1 x2) $ testTerm t1 t2
testConstr (Pair a1 b1)(Pair a2 b2) = (&&) <$> testConc a1 a2 <*> testConc b1 b2
testConstr (Pi x1 a1 t1) (Pi x2 a2 t2) = testConc a1 a2 <&> (local (addAlias' x1 x2) $ testTerm t1 t2)
testConstr (Sigma x1 a1 t1) (Sigma x2 a2 t2) = testConc a1 a2 <&> (local (addAlias' x1 x2) $ testTerm t1 t2)
testConstr (Tag t1)(Tag t2) = return $ t1 == t2
testConstr (Fin ts1)(Fin ts2) = return $ ts1 == ts2
testConstr (Universe x1)(Universe x2) = return $ x1 == x2


