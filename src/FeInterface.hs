{-# LANGUAGE OverloadedStrings, ExistentialQuantification, RecordWildCards #-}
module FeInterface where

import Display
import TCM

data FrontEnd = forall token modul. Pretty token => FE {
  myLLexer :: String -> [token],
  pModule :: [token] -> Either String modul,
  resolveModule :: modul -> Either String (Term',Term')
  }
