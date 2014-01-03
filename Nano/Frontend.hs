{-# LANGUAGE OverloadedStrings, ExistentialQuantification, RecordWildCards #-}
module Nano.Frontend where

import qualified Nano.Abs as A
import Nano.Par
import Nano.Lex
import Nano.Layout
import Nano.ErrM
import Nano.Resolve
import Display
import FeInterface

instance Pretty Token where
    pretty = text . show

errToEither (Ok x) = Right x
errToEither (Bad x) = Left x

fe = FE { pModule = errToEither . Nano.Par.pModule,
          resolveModule = Nano.Resolve.resolve,
          myLLexer = resolveLayout True . myLexer}
