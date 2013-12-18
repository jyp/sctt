-- | Double checking values.

module Check where

import Data.Set (Set)
import qualified Data.Set as Set

import Value

-- * Contexts and heaps

data CxtEntry = CxtEntry { cxtHyp :: Hyp, cxtTyp :: Conc } -- ^ @x : Y_@.

newtype Cxt = Cxt { cxt :: [CxtEntry] }

newtype Heap = Heap { heap :: Binds }

-- * Constraints

data Constraint = Constraint { cTag :: Tag, cHyp :: Hyp } -- ^ @'t = x@.

newtype Constraints = Constraints { constraints :: [Constraint] }

-- * Type-checking monad

-- | Type-checking environment.
data Env = Env
  { envCxt         :: Cxt
  , envHeap        :: Heap
  , envConstraints :: Constraints
  }

-- | Type-checking error.
type TCErr = String

-- | Type-checking monad.
newtype CheckM a = CheckM { checkM :: ReaderT Env (Either TCErr a) }

-- * Type-checking algorithm

-- | Look up a hypothesis in the heap.
lookHyp :: Hyp -> CheckM

whnf :: Term -> CheckM RTerm

infer :: LTerm -> CheckM Type
infer d =
  case d of
    LHyp x -> lookHyp x >>= \case
      IsHyp   a -> return a
      IsAlias y -> infer y
    App x y_ -> infer x >>= \case

