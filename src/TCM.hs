{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, OverloadedStrings, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
module TCM where

import Terms
import TermsInstances()
import Ident
import Fresh
import Display
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.RWS
import Control.Monad.Error
import Control.Applicative
import Data.Map (Map)

type Term' = Term Id Id
type Constr' = Constr Id Id
type Destr' = Destr Id
type Heap' = Heap Id Id
type Branch' = Branch Id Id
type Val' = Val Id Id

data Heap n r = Heap { dbgDepth :: Int
                     , definitions :: [(r,Val n r)] -- should be congruence-closure
                     , aliases :: Map r r -- should be union-find
                     , context :: Map r r -- Mapping
                     }
instance (Pretty r, Pretty n) => Pretty (Heap n r) where
  pretty (Heap {..}) = sep [hang lab 2  v
                           | (lab,v) <- [("defs" ,pretty definitions)
                                        ,("aliases" ,pretty aliases)
                                        ,("context",pretty context)]
                             ]

newtype TC a = TC {fromTC :: ErrorT Doc (RWST Heap' [Doc] () FreshM) a}
  deriving (Functor, Applicative, Monad, MonadReader Heap', MonadWriter [Doc], MonadError Doc)

instance Error Doc where
  noMsg = "unknown error"
  strMsg = text

runTC :: Unique -> Heap' -> TC a -> (Either Doc a,[Doc])
runTC u h0 (TC x) = runFreshMFromUnique u $ evalRWST (runErrorT x) h0 ()

liftTC :: FreshM a -> TC a
liftTC x = TC $ lift $ lift x

substTC xx a_ bb = liftTC (subst xx a_ bb)

substByDestr :: (r~Id,n~Id) => Hyp r -> Destr r -> Term n r -> TC (Term n r)
substByDestr h d t = do
  x' <- liftTC $ refreshId h
  t' <- substTC h x' t
  return $ Destr x' d t'

terr :: Doc -> TC a
terr msg = do
  h <- ask
  throwError $ sep [hang "heap" 2 (pretty h), msg]

report :: Doc -> TC ()
report msg = do
  lvl <- dbgDepth <$> ask
  tell [text (replicate lvl ' ') <> msg]
