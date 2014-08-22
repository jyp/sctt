{-# LANGUAGE RecordWildCards, GADTs, OverloadedStrings, TypeSynonymInstances, FlexibleInstances, RecordWildCards, ViewPatterns, PatternGuards #-}

module Heap (emptyHeap, addDef,addCut,lookHeapC,getAlias,enter,addAlias',aliasOf,pConc,pHyp,addAlias) where

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

addTermDef' :: (Monoid a,Id~n,Id~r,Ord n) => n -> Val n r -> Term n n -> Maybe (Heap n r)
addTermDef' = error "addTermDef"

addTermDef :: (Monoid a) => Id -> Term' -> TC a -> TC a
addTermDef = error "addTermDef"

app :: Monoid a => Val Id Id -> Id -> (Term' -> TC a) -> TC a
app lam arg k = do
  (VLam x t) <- liftTC (refreshBinders lam)
  addCut x arg (k t)

-- 1st arg is the hypothesis (may be eliminated somewhere); 2nd arg the conclusion
addCut :: Monoid a => Id -> Id -> TC a -> TC a
addCut hyp concl k = do
  Heap{..} <- ask
  case lookup concl definitions of
    Nothing -> case lookup hyp definitions of
      Nothing -> addAlias hyp concl k
      Just def -> addDef concl def k
    Just def -> addDef hyp def k

applyAliases :: Val' -> TC (Val')
applyAliases = error "arouwfydt"

partitionWith :: (a -> Either b c) -> [a] -> ([b],[c])
partitionWith f xs = partitionEithers (map f xs)

redex :: Monoid a => Id -> Val' -> Id -> TC a -> TC a
redex result fun arg k = app fun arg $ \t' -> addTermDef result t' k

addDef ::  Monoid a => Id -> Val' -> TC a -> TC a
addDef r d0 k = do
  d <- applyAliases d0
  Heap{..} <- ask
  case [r' |(r',d') <- definitions, d == d'] of
    (r':_) -> addAlias r r' k
    [] -> local (\h -> h {definitions = (r,d):definitions}) $
            case d of
                VApp f a | Just lam <- lookup f definitions -> redex r lam a k
                    -- Is there a definition for the thing being eliminated? Then reduce.
                VHyp y -> addAlias r y k
                VLam x t -> do
                  -- find all eliminators and evaluate them.
                  let rest :: [(Id,Val')]
                      (ra, rest) = partitionWith (\(r',d') -> case d' of {VApp f a | f == r -> Left (r',a); otherwise -> Right (r',d')}) definitions
                      go [] k = k
                      go ((ret,arg):ras) k = redex ret d arg (go ras k)
                  go ra $ local (\h -> h {definitions = (r,d):rest}) k
                VPair x y -> do
                   let pairs = [(x',y') | (r',VPair x' y') <- definitions, r == r']
                       go [] k = k
                       go ((x',y'):ps) k = addAliases [(x,x'),(y,y')] $ go ps k
                       -- we can keep all the defs here; aliasing mechanism will take care of cleaning them up.
                   go pairs k
                VTag t -> case lookup r definitions of -- is the variable given another tag value?
                  Just (VTag t') | t == t'  -> return mempty -- Then the heap is inconsistent.
                  Nothing -> k
                _ -> k -- nothing special to do.

addAlias' :: Ord r => r -> r -> M.Map r r -> M.Map r r
addAlias' src trg as = f <$> M.insert src trg as
  where f x = if x == src then trg else x

addAliases' :: Ord r => [(r,r)] -> M.Map r r -> M.Map r r
addAliases' = foldr (.) id . map (uncurry addAlias')


getAlias as x = case M.lookup x as of
  Just h' -> h'
  Nothing -> x

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

aliasOf x = flip getAlias x . aliases <$> ask

-- | Look for some constructed value in the heap.
lookHeapC :: (r~Id,n~Id) => Conc n -> TC (Val n r)
lookHeapC (Conc x) = do
  h <- ask
  x' <- aliasOf x
  let lk = lookup x' (definitions h)
  case lk of
    Nothing -> terr $ "Construction not found: " <> pretty x
    Just c -> return c

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
