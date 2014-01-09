module Fresh where

import Control.Applicative hiding (empty)
import Control.Monad.State
import Control.Arrow ((&&&))
import Ident
import Data.Bifoldable

import Data.Bitraversable
import Data.Bifunctor
import Data.Maybe (fromMaybe)
fromNames ::  Bitraversable p => p Name Name -> p Id Id
fromNames = fromNamesFlag True

fromNamesLiberal ::  Bitraversable p => p Name Name -> p Id Id
fromNamesLiberal = fromNamesFlag False

fromNamesFlag :: Bitraversable p => Bool -> p Name Name -> p Id Id
fromNamesFlag safe x = runFreshM (evalStateT (bitraverse fresh_name look x) [])
  where
    fresh_name s = do
       x <- lift fresh
       let r = Id s x Nothing
       modify ((s,r):)
       return r
    look s = do
      m <- get
      case lookup s m of
        Nothing ->
          if safe
              then error $ "Unknown identifier : " ++ s
              else fresh_name s
        Just x -> return x

names :: Bifoldable t => t name ref -> [name]
names = biconcatMap (\ n -> [n]) (\ _r -> [])

refreshBinders :: (Bifunctor t,Bifoldable t) => t Id Id -> FreshM (t Id Id)
refreshBinders s = do
    freshened <- sequence [ (,) b <$> refreshId b | b <- names s ]
    let lk x = fromMaybe x (lookup x freshened)
    return $ bimap lk lk $ s

rSubst :: (Bifunctor t, Eq r) => r -> r -> t n r -> t n r
rSubst r0 r1 = bimap id (\r -> if r == r0 then r1 else r)

subst :: (Bifoldable t, Bifunctor t) => Id -> Id -> t Id Id -> FreshM (t Id Id)
subst x r t = rSubst x r <$> refreshBinders t

-- | New fresh Id
fresh :: FreshM Unique
fresh = state (Unique &&& succ)


freshId :: FreshM Id
freshId = do u <- fresh
             return $ mkId "tmp" u

freshFrom :: Name -> FreshM Id
freshFrom n = do u <- fresh
                 return $ mkId n u

freshIds :: Int -> FreshM [Id]
freshIds n = replicateM n freshId

refreshId :: Id -> FreshM Id
refreshId x = do
    u <- fresh
    return x { id_unique = u }

infixl 4 <.>
-- | Applies a pure value in an applicative computation
(<.>) :: Applicative f => f (a -> b) -> a -> f b
m <.> x = m <*> pure x

type FreshM = State Int

runFreshM :: FreshM a -> a
runFreshM m = evalState m 0

runFreshMFromUnique :: Unique -> FreshM a -> a
runFreshMFromUnique (Unique n) m = evalState m n

runFreshMFrom :: Bifoldable t => t Id Id -> FreshM a -> a
runFreshMFrom = runFreshMFromUnique . nextUnique

nextUnique :: Bifoldable t => t Id Id -> Unique
nextUnique = succ . maximum . map Ident.id_unique . biList

