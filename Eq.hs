{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs #-}

import Terms
import qualified Data.Map as M

import Control.Monad.Reader
import Control.Applicative


-- TODO: check that a variable has not two different Tag constr/destr

newtype M n r a = M (Reader (Heap n r) a)
  deriving (Functor, Applicative, Monad, MonadReader (Heap n r))

addAlias' :: Ord r => r -> r -> Heap n r -> Heap n r
addAlias' src trg h@Heap{..} = h{heapAlias = f <$> M.insert src trg heapAlias }
  where f x = if x == src then trg else x

addAliases' :: Ord r => [(r,r)] -> Heap n r -> Heap n r
addAliases' = foldr (.) id . map (uncurry addAlias')

addConstr' :: Ord n => n -> Constr n r -> Heap n r -> Heap n r
addConstr' src trg h@Heap{..} = h{heapConstr = M.insert src trg heapConstr }

addDestr' :: Ord r => Destr r -> n -> Heap n r -> Heap n r
addDestr' src trg h@Heap{..} = h{heapDestr = M.insert src trg heapDestr }


getAlias x = M.findWithDefault x x

addAliases :: Ord r => [(r,r)] -> M n r Bool -> M n r Bool
addAliases [] k = k
addAliases as k = do
  h <- addAliases as <$> ask
  
  let hD' = M.mapKeysWith (++) (map (getAlias $ heapAlias h) ) $ map (:[]) $ heapDestr h
      TODO: look everywhere for non-singleton lists, genereating new sets of aliases.
  k
-- TODO: transitive search of stuff.
-- Possible algo. : use (mapKeys . map (:[])) on heapDestr, this generates a new set of aliases to apply.

addAlias :: Ord r => r -> r -> M n r Bool -> M n r Bool
addAlias src trg k = undefined
-- TODO: transitive search of stuff.
-- Possible algo. : use (mapKeys . map (:[])) on heapDestr, this generates a new set of aliases to apply.

aliasOf :: Ord r => r -> M n r r
aliasOf x = getAlias <$> asks heapAlias

lookHeapC :: Ord n => n -> M n r (Constr n r)
lookHeapC x = do
  cHeap <- asks heapConstr
  case M.lookup x cHeap of
    Just c -> return c

-- | return true if fizzled, otherwise call the continuation.
addDestr :: (n ~ r, Ord r) =>  Hyp n -> Destr r -> M n r Bool -> M n r Bool
addDestr x d k = do
  dHeap <- asks heapDestr
  case M.lookup d dHeap of
    Just y -> addAlias y x k
    Nothing -> local (addDestr' d x) k


-- | return true if fizzled, otherwise call the continuation.
    -- for now we assume normal forms so adding a construction should never trigger anything.
addConstr :: Ord n => Conc n -> Constr n r -> M n r Bool -> M n r Bool
addConstr x c k = do
  local (addConstr' x c) k

(<&>) :: Applicative a => a Bool -> a Bool -> a Bool
x <&> y = (&&) <$> x <*> y


testTerm :: (n ~ r, Ord r) =>  Term n r -> Term n r -> M n r Bool
testTerm (Conc c1)(Conc c2) = (==) <$> aliasOf c1 <*> aliasOf c2
testTerm (Destr x d t1) t2 = addDestr x d (testTerm t1 t2)
testTerm (Constr x c t1) t2 = addConstr x c (testTerm t1 t2)
testTerm (Case x bs) t2 = and <$> forM bs (\(Br tag t1) ->
  addConstr x (Tag tag) $ addDestr x (Tag' tag) $ testTerm t1 t2)
testTerm c1 c2 = testTerm c2 c1

testConc :: (n ~ r, Ord r) => Conc r -> Conc r -> M n r Bool
testConc a1 a2 = do
  c1 <- lookHeapC a1
  c2 <- lookHeapC a2
  testConstr c1 c2

testConstr :: (n ~ r, Ord r) => Constr n r -> Constr n r -> M n r Bool
testConstr (Done h1) (Done h2) = (==) <$> aliasOf h1 <*> aliasOf h2
testConstr (Alias' c1) c2 = testConstr c2 =<< lookHeapC c1
testConstr c1 (Alias' c2) = testConstr c1 =<< lookHeapC c2
testConstr (Lam x1 t1) (Lam x2 t2) = local (addAlias' x1 x2) $ testTerm t1 t2
testConstr (Pair a1 b1)(Pair a2 b2) = (&&) <$> testConc a1 a2 <*> testConc b1 b2
testConstr (Pi x1 a1 t1) (Pi x2 a2 t2) = testConc a1 a2 <&> (local (addAlias' x1 x2) $ testTerm t1 t2)
testConstr (Sigma x1 a1 t1) (Sigma x2 a2 t2) = testConc a1 a2 <&> (local (addAlias' x1 x2) $ testTerm t1 t2)
testConstr (Tag t1)(Tag t2) = return $ t1 == t2
testConstr (Fin ts1)(Fin ts2) = return $ ts1 == ts2
testConstr (Universe x1)(Universe x2) = return $ x1 == x2


