{-# LANGUAGE RecordWildCards, GADTs, OverloadedStrings, TypeSynonymInstances, FlexibleInstances, RecordWildCards, ViewPatterns, PatternGuards #-}

module Heap where

import Control.Monad.RWS
import Control.Applicative

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
addConstr c d k = case d of
  (Hyp h) -> addAlias c h k
  (Lam x t) -> addDef c (VLam x t) k
  (Q q x t u) -> do y <- liftTC $ freshId
                    addDef y (VLam x u) $ addDef c (VQ q t y) k
  (Pair x y) -> addDef c (VPair x y) k
  (Tag x) -> addDef c (VTag x) k
  (Fin x) -> addDef c (VFin x) k
  (Universe x) -> addDef c (VUniv) k

addDestr :: Monoid a => Id -> Destr' -> TC a -> TC a
addDestr h d = case d of
  App f ( a) -> addDef h (VApp f a)
  Cut ( c) _typ -> addAlias h c

addTermDef :: (Monoid a) => Id -> Term' -> TC a -> TC a
addTermDef x t k = onConcl t $ \( c) -> addAlias x c k

app :: Monoid a => Val' -> Id -> (Id -> TC a) -> TC a
app fun arg k = do
  fun' <- liftTC (refreshBinders fun)
  case fun' of
    VLam x t -> do
      t' <- substTC x arg t
      onConcl t' $ k -- (VClosure arg t')
    _ -> terr $ "panic: app: expected lambda but got " <> pretty fun'

checkCuts :: Monoid a => [Id] -> TC a -> TC a
checkCuts [] = id
checkCuts (x:xs) = checkCut x . checkCuts xs

checkCut :: Monoid a => Id -> TC a -> TC a
checkCut v0 k = do
  v <- aliasOf v0
  mdef <- lookHeap v
  case mdef of
    Nothing -> k -- if there is no definition; there can't be a reduction.
    Just def -> wakeClosures v $ do
       Heap {..} <- ask
       case def of
         VLam _ _ -> do
           -- find all eliminators and evaluate them.
           let ra = [(r',a) | (r',VApp f a) <- definitions, f == v]
               go [] k = k
               go ((ret,arg):ras) k = redex ret def arg (go ras k)
           go ra k
         VPair x y -> do
            let pairs = [(x',y') | (v',VPair x' y') <- definitions, v == v']
                go [] k = k
                go ((x',y'):ps) k = addAlias x x' $ addAlias y y' $ go ps k
                -- we can keep all the defs here; aliasing mechanism will take care of cleaning them up.
            go pairs k
         VTag t -> case [t' | (v',VTag t') <- definitions, v == v', t /= t'] of -- is the variable given another tag value?
           [] -> k
           _:_ -> return mempty -- Then the heap is inconsistent.
         _ -> k -- No eliminable construction found: nothing special to do.

partitionWith :: (a -> Either b c) -> [a] -> ([b],[c])
partitionWith f xs = partitionEithers (map f xs)

isCon :: Val t t1 -> Bool
isCon v = case v of
  VApp _ _ -> False
  VClosure _ _ -> False
  _ -> True

redex :: Monoid a => Id -> Val' -> Id -> TC a -> TC a
redex result fun arg k = app fun arg $ \clos -> addAlias result clos k

wakeClosures :: Monoid a => Id -> TC a -> TC a
wakeClosures a k = do
  Heap{..} <- ask
  let (closures, rest) = partitionWith (\(r',d') -> case d' of {VClosure a' t | a' == a -> Left (r',t);
                                                                _ -> Right (r',d')}) definitions
      go [] k = k
      go ((ret,t):rts) k = addTermDef ret t $ go rts k
  local (\h -> h {definitions = rest}) $ go closures k

addDef ::  Monoid a => Id -> Val' -> TC a -> TC a
addDef r0 d0 k = do
  r <- aliasOf r0
  d <- applyAliases d0
  Heap{..} <- ask
  case [r' | (r',d') <- definitions, d == d'] of
    (r':_) -> addAlias r r' k
    [] -> do
      report $ "Added def: " <> pretty r <> " = " <> pretty d
      local (\h -> h {definitions = (r,d):definitions}) $ case d of
        VClosure x t -> case [() | (x',v) <- definitions, x == x', isCon v] of
          [] -> k
          _ -> local (\h -> h {definitions = definitions}) $ addTermDef r t k
               -- if there is a construction for the arg, expand the closure.
        VApp f a | Just lam <- lookup f (filter (isCon . snd) definitions) -> redex r lam a k
            -- Is there a definition for the thing being eliminated? Then reduce.
        _ -> checkCut r k

swap (x,y) = (y,x)

addAliases :: Monoid a => [(Id,Id)] -> TC a -> TC a
addAliases = foldr (.) id . map (uncurry addAlias)

addAlias :: Monoid a => Id -> Id -> TC a -> TC a
addAlias src trg0 k = do
  trg <- aliasOf trg0
  if trg == src
     then k
     else do
       h <- ask
       let applyAlias x = if x == src then trg else x
           defs' :: [(Id,Val Id Id)]
           defs' =  fmap (applyAlias <$>) <$> definitions h
           ctx' = M.fromList [(applyAlias s, applyAlias t) | (s,t) <- M.assocs $ context h]
           hD' :: M.Map (Val Id Id) [Id]
           hD' = M.fromListWith (++) [(d, [x]) | (x,d) <- defs']
           myhead (x:_) = x
           hD'' = fmap myhead hD'
           classes = M.elems hD'
           extraAliases = [(x,y) | (x:xs) <- classes, y <- xs]
       local (\h2 -> h2 {aliases = M.insert src trg (aliases h2), definitions = defs', context = ctx'}) $
         checkCut trg $ addAliases extraAliases k

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
lookHeap :: (r~Id,n~Id) => n -> TC (Maybe (Val n r))
lookHeap = lkHeap isCon

lkHeap :: (r~Id,n~Id) => (Val n r -> Bool) -> n -> TC (Maybe (Val n r))
lkHeap p x = do
  h <- ask
  x' <- aliasOf x
  return $ lookup x' (filter (p . snd) $ definitions h)

instance Monoid Bool where
  mempty = True
  mappend = (&&)

-- | Pretty printing

class Prettier a where
  prettier :: a -> TC Doc

pConc = pHyp

pHyp :: Hyp Id -> TC Doc
pHyp x = do
  h <- ask
  let lk = lookup (getAlias (aliases h) x) $ definitions h -- fixme: should look for "best" definition; including reverse pairs.
  case lk of
    Nothing -> return $ pretty x
    Just d -> prettier d

instance Prettier Val' where
  prettier = return . pretty

instance Prettier Term' where
  prettier = return . pretty
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
  prettier (Q Pi x t b) = do
    t' <- pConc t
    b' <- prettier b
    return $ (parens (pretty x <>":"<> t') <+> "->") $$+ b'
  prettier (Q Sigma x t b) = do
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
