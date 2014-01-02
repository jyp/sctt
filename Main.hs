{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings, ExistentialQuantification, RecordWildCards #-}
module Main where

import Data.Either
import Options

import Micro.Frontend
import TypeCheck
import Control.Monad.Error
import Display
import TCM
import FeInterface
import Micro.Frontend

chooseFrontEnd :: FilePath -> FrontEnd
chooseFrontEnd _ = fe

type Verbosity = Int

putStrV :: Verbosity -> Doc -> Checker ()
putStrV v s = if verb options >= v then liftIO $ putStrLn (render s) else return ()

runFile :: FilePath -> Checker ()
runFile f = do
  let fe = chooseFrontEnd f
  putStrV 1 $ "Processing file:" <+> text f
  contents <- liftIO $ readFile f
  run fe contents f

type Checker a = ErrorT Doc IO a

run :: FrontEnd -> String -> FilePath -> Checker ()
run fe@FE{..} s fname = let ts = myLLexer s in case pModule ts of
   Left err -> do
     putStrV 1 $ "Tokens:" <+> pretty ts
     throwError $ text $ fname ++ ": parse failed: " ++ err
   Right tree -> do
      let Right (rTyp,rVal) = resolveModule tree
      putStrV 4 $ "[Resolved value]" $$ pretty rVal
      putStrV 4 $ "[Resolved type]" $$ pretty rTyp
      let (res,info) = typeCheck rVal rTyp
      mapM_ (putStrV 0) info
      case res of
        Left err -> throwError err
        Right _ -> return ()

main :: IO ()
main = do
  results <- forM (files options) $ \f -> runErrorT $ runFile f
  let (errs,oks) = partitionEithers results
  mapM_ (putStrLn . render) errs
  putStrLn $ show (length oks) ++ "/" ++ show (length results) ++ " files typecheck."

