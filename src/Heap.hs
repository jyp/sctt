{-# LANGUAGE RecordWildCards, GADTs, OverloadedStrings, TypeSynonymInstances, FlexibleInstances, RecordWildCards, ViewPatterns, PatternGuards #-}

module Heap where

import Control.Monad.RWS
import Control.Applicative

import Data.Bifunctor
import qualified Data.Map as M
import Data.Either

import Terms
import Ident
import Display
import TCM
import Fresh

emptyHeap :: Heap n r
emptyHeap = Heap 0 [] M.empty M.empty

enter :: TC a -> TC a
enter = local (\h@Heap{..} -> h {dbgDepth = dbgDepth + 1})

onConcl :: Monoid a => Term' -> (Conc Id -> TC a) -> TC a
onConcl (Concl c)       k = k c
onConcl (Destr x d t1)  k = addDestr x d (onConcl t1 k)
onConcl (Constr ( x) c t1) k = addConstr x c (onConcl t1 k)
onConcl (Split x y z t1) k = addSplit x y z $ onConcl t1 k
onConcl (Case x bs)     k = mconcat <$> do
    forM bs $ \(Br tag t1) ->
      addTag x tag $ onConcl t1 k

addTag :: Monoid a => Hyp Id -> String -> TC a -> TC a
addTag x t k = addDef x (VTag t) k

addSplit :: (Monoid a,r~Id,n~Id) => Hyp r -> Hyp r -> Hyp n -> TC a -> TC a
addSplit x y z k = addDef z (VPair x y) k

addConstr :: Monoid a => Id -> Constr' -> TC a -> TC a
addConstr c d = addDef c $ case d of
  -- (Hyp h) -> (VHyp h)
  (Lam x t) -> (VLam x t)
  -- (Pi x t u) -> Pi t (VLam x u)
  -- TODO

addDestr :: Monoid a => Id -> Destr' -> TC a -> TC a
addDestr h d = case d of
  App f ( a) -> addDef h (VApp f a)
  Cut ( c) _typ -> addCut h c

addTermDef :: (Monoid a) => Id -> Term' -> TC a -> TC a
addTermDef x t k = onConcl t $ \( c) -> addCut x c k


app :: Monoid a => Val Id Id -> Id -> (Val' -> TC a) -> TC a
app fun arg k = do
  VLam x t <- liftTC (refreshBinders fun)
  t' <- substTC x arg t
  k (VClosure arg t')

-- 1st arg is the hypothesis (may be eliminated somewhere); 2nd arg the conclusion
addCut :: Monoid a => Id -> Id -> TC a -> TC a
addCut hyp concl k = do
  h' <- lookHeap hyp
  c' <- lookHeap concl
  case h' of
    Nothing -> case c' of
      Nothing -> addAlias hyp concl k
      Just def -> addDef concl def k
    Just def -> addDef hyp def k

partitionWith :: (a -> Either b c) -> [a] -> ([b],[c])
partitionWith f xs = partitionEithers (map f xs)

isCon :: Val t t1 -> Bool
isCon v = case v of
  VLam _ _ -> True
  VPair _ _ -> True
  VTag _ -> True
  VPi _ _ -> True
  VSigma _ _-> True
  VFin _ -> True
  VUniv _ -> True
  _ -> False

redex :: Monoid a => Id -> Val' -> Id -> TC a -> TC a
redex result fun arg k = app fun arg $ \clos -> addDef result clos k

wakeClosures :: Monoid a => Id -> TC a -> TC a
wakeClosures a k = do
  Heap{..} <- ask
  let (closures, rest) = partitionWith (\(r',d') -> case d' of {VClosure a' t | a' == a -> Left (r',t);
                                                                _ -> Right (r',d')}) definitions
      go [] k = k
      go ((ret,t):rts) k = addTermDef ret t $ go rts k
  local (\h -> h {definitions = rest}) $ go closures k

addDef ::  Monoid a => Id -> Val' -> TC a -> TC a
addDef r d0 k = do
  d <- applyAliases d0
  Heap{..} <- ask
  error "FIXME: unblock closures when necessary"
  case [r' |(r',d') <- definitions, d == d'] of
    (r':_) -> addAlias r r' k
    [] -> local (\h -> h {definitions = (r,d):definitions}) $
            case d of
                VClosure x t -> case [() | (x',v) <- definitions, x == x', isCon v] of
                  [] -> k
                  _ -> local (\h -> h {definitions = definitions}) $ addTermDef r t k
                VApp f a | Just lam <- lookup f definitions -> redex r lam a k
                    -- Is there a definition for the thing being eliminated? Then reduce.
                -- VHyp y -> addAlias r y k
                VLam _x _t -> do
                  -- find all eliminators and evaluate them.
                  let rest :: [(Id,Val')]
                      (ra, rest) = partitionWith (\(r',d') -> case d' of {VApp f a | f == r -> Left (r',a);
                                                                          _ -> Right (r',d')}) definitions
                      go [] k = k
                      go ((ret,arg):ras) k = redex ret d arg (go ras k)
                  local (\h -> h {definitions = (r,d):rest}) $ go ra $ wakeClosures r k
                VPair x y -> do
                   let pairs = [(x',y') | (r',VPair x' y') <- definitions, r == r']
                       go [] k = k
                       go ((x',y'):ps) k = addAliases [(x,x'),(y,y')] $ go ps $ wakeClosures r k
                       -- we can keep all the defs here; aliasing mechanism will take care of cleaning them up.
                   go pairs k
                VTag t -> case lookup r definitions of -- is the variable given another tag value?
                  Just (VTag t') | t == t'  -> return mempty -- Then the heap is inconsistent.
                  Nothing -> wakeClosures r k
                _ -> k -- nothing special to do.


addAlias' :: Ord r => r -> r -> M.Map r r -> M.Map r r
addAlias' src trg as = f <$> M.insert src trg as
  where f x = if x == src then trg else x

addAliases' :: Ord r => [(r,r)] -> M.Map r r -> M.Map r r
addAliases' = foldr (.) id . map (uncurry addAlias')


swap (x,y) = (y,x)
addAliases :: [(Id,Id)] -> TC a -> TC a
addAliases [] k = k
addAliases as k = do
  h <- ask
  report $ ("Adding aliases:" $$+ pretty as)
  origAliases <- aliases <$> ask
  let allAliases = addAliases' as origAliases
  let applyAlias = getAlias allAliases
      hD' :: M.Map (Val Id Id) [Id]
      hD' = M.fromListWith (++) [(fmap applyAlias d, [x]) | (x,d) <- definitions h]
      myhead (x:_) = x
      hD'' = fmap myhead hD'
      classes = M.elems hD'
      aliases = [(x,y) | (x:xs) <- classes, y <- xs]
      defs' :: [(Id,Val Id Id)]
      defs' =  fmap (applyAlias <$>) <$> definitions h
  local (\h2 -> h2 {aliases = allAliases, definitions = defs'}) $
    addAliases aliases k

addAlias :: Id -> Id -> TC a -> TC a
addAlias src trg = addAliases [(src,trg)]

getAlias :: Ord a => M.Map a a -> a -> a
getAlias as x = case M.lookup x as of
  Just h' -> h'
  Nothing -> x

aliasOf :: Id -> TC Id
aliasOf x = flip getAlias x . aliases <$> ask

applyAliases :: Val' -> TC (Val')
applyAliases v = do
  as <- aliases <$> ask
  return (fmap (getAlias as) v)

-- | Look for some constructed value in the heap.
lookHeapC :: (r~Id,n~Id) => Conc n -> TC (Val n r)
lookHeapC ( x) = do
  lk <- lookHeap x
  case lk of
    Nothing -> terr $ "Construction not found: " <> pretty x
    Just c -> return c

-- | Look for some constructed value in the heap.
lookHeap :: (r~Id,n~Id) => n -> TC (Maybe (Val n r))
lookHeap x = do
  h <- ask
  x' <- aliasOf x
  return $ lookup x' (definitions h)

instance Monoid Bool where
  mempty = True
  mappend = (&&)

-- | Pretty printing

class Prettier a where
  prettier :: a -> TC Doc

pConc :: Conc Id -> TC Doc
pConc x = prettier =<< lookHeapC x

pHyp :: Hyp Id -> TC Doc
pHyp x = do
  h <- ask
  let lk = lookup (getAlias (aliases h) x) $ definitions h
  case lk of
    Nothing -> return $ pretty x
    Just d -> prettier d

instance Prettier Val' where

instance Prettier Term' where
  -- prettier (Concl c) = pConc c
  -- prettier (Destr h d t) = addDef h d $ prettier t
  -- prettier (Constr x c t) = addConstr x c $ prettier t
  -- prettier (Split x y z t) = do
  --   z' <- pHyp z
  --   t' <- prettier t
  --   return $ ("split " <> z' <> "into " <> pretty x <> "," <> pretty y $$ t')
  -- prettier (Case x bs) = do
  --   bs' <- mapM prettier bs
  --   h <- pHyp x
  --   return $ ("case" <+> h <+> "of {") $$+ (sep $ punctuate "." $ bs') $$ "}"

instance Prettier Constr' where
  prettier (Hyp h) = pHyp h
  prettier (Lam x b) = do
    b' <- prettier b
    return $ ("\\" <> pretty x <> " ->") $$+ b'
  prettier (Pi x t b) = do
    t' <- pConc t
    b' <- prettier b
    return $ (parens (pretty x <>":"<> t') <+> "->") $$+ b'
  prettier (Sigma x t b) = do
    t' <- pConc  t
    b' <- prettier b
    return $ parens (pretty x <>":"<> t') <> " × " <> b'
  prettier (Pair a b) = do
    a' <- pConc  a
    b' <- pConc  b
    return $ parens $ a' $$+ "," $$+ b'
  prettier x = return $ pretty x

instance Prettier Destr' where
  prettier (App f x) = do
    f' <- pHyp f
    x' <- pConc x
    return $ f' <+> x'
  prettier (Cut x t) = do
    x' <- pConc x
    t' <- pConc t
    return $ x' <+> ":" <+> t'

instance Prettier Branch' where
  prettier (Br tag t) = (\x -> ("'" <> text tag <> " ->") $$+ x) <$> prettier t
