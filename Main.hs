{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Data.Either
import Options

import qualified Nano.Abs as A
import Nano.Par
import Nano.Lex
import Nano.Layout
import Nano.ErrM
import Resolve
import TypeCheck
import System.FilePath
import Control.Monad.Error
import Display
import Eq

instance Error Doc where
  noMsg = "nanoAgda: unknown error"
  strMsg = text

myLLexer :: String -> [Token]
myLLexer = resolveLayout True . myLexer

type Verbosity = Int

putStrV :: Verbosity -> Doc -> Checker ()
putStrV v s = if verb options >= v then liftIO $ putStrLn (render s) else return ()

-- | The file containing the type of the term contained in file @f@
typeFile :: FilePath -> FilePath
typeFile f = replaceExtension f "type.na"

runFile :: FilePath -> Checker (Term')
runFile f = do
  putStrV 1 $ "Processing file:" <+> text f
  contents <- liftIO $ readFile f
  run contents f

instance Pretty Token where
    pretty = text . show

type Checker a = ErrorT Doc IO a

run :: String -> FilePath -> Checker (Term')
run s fname = let ts = myLLexer s in case pTerm ts of
   Bad err -> do
     putStrV 1 $ "Tokens:" <+> pretty ts
     throwError $ text $ fname ++ ": parse failed: " ++ err
   Ok tree -> do
     process fname tree

process :: FilePath -> A.Term -> Checker (Term')
process fname modul = do
  let resolved = resolve modul
  putStrV 4 $ "[Resolved into]" $$ text (show resolved)
  let (accept,info) = checkTyp resolved
  mapM_ (putStrV 0) info
  guard accept
  return resolved
  
main :: IO ()
main = do
  results <- forM (files options) $ \f -> runErrorT $ runFile f
  let (errs,oks) = partitionEithers results
  mapM_ (putStrLn . render) errs
  putStrLn $ show (length oks) ++ "/" ++ show (length results) ++ " files typecheck."

