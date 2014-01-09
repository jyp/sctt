{-# LANGUAGE OverloadedStrings, ExistentialQuantification, RecordWildCards #-}
module Micro.Frontend where

import qualified Micro.Abs as A
import Micro.Par
import Micro.Lex
import Micro.Layout
import Micro.ErrM
import Micro.Resolve
import Display
import FeInterface

instance Pretty Token where
    pretty = text . show

errToEither (Ok x) = Right x
errToEither (Bad x) = Left x

fe = FE { pModule = errToEither . Micro.Par.pModule,
          resolveModule = Micro.Resolve.resolve,
          myLLexer = resolveLayout True . myLexer}
