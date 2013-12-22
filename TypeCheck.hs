{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables #-}
module Eq where
import Terms
import qualified Data.Map as M

import Control.Monad.Reader
import Control.Applicative


-- Infer the type of a destruction
inferDestr :: Destr r -> M n r (Conc r)

-- Direct lookup in the context
inferHyp :: Hyp r -> M n r (Term n r)

-- splice some bindings into the heap and continue with the
-- conclusion
spliceBinding :: Term n r -> (Constr n r -> M n r a) -> M n r a
--todo: maintain the invariant that every hyp. has an entry in the context.

checkTermAgainstTerm :: Term n r -> Term n r -> M n r ()

checkConAgainstTerm :: Constr n r -> Term n r -> M n r ()

checkConAgainstCon :: Constr n r -> Constr n r -> M n r ()
