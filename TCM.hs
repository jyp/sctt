{-#LANGUAGE NamedFieldPuns, RecordWildCards, GeneralizedNewtypeDeriving, GADTs, ScopedTypeVariables, OverloadedStrings, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
module TCM where

import Terms
import Ident
import Fresh
import Display
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.RWS
import Control.Monad.Error
import Control.Applicative

type Heap' = Heap Id Id

newtype TC a = TC {fromTC :: ErrorT String (RWST Heap' [Doc] () FreshM) a} 
  deriving (Functor, Applicative, Monad, MonadReader Heap', MonadWriter [Doc])


