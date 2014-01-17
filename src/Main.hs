{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings, ExistentialQuantification, RecordWildCards, TupleSections #-}
module Main where

import Data.Either
{-# LANGUAGE TupleSections #-}
import Options
import TypeCheck
import Control.Monad.Error
import Control.Applicative
import Display
import TCM
import FeInterface
import qualified Micro.Frontend
import qualified Nano.Frontend
import System.FilePath


chooseFrontEnd :: FilePath -> FrontEnd
chooseFrontEnd p = case takeExtension p of
  ".na" -> Nano.Frontend.fe
  ".ma" -> Micro.Frontend.fe

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
run FE{..} s fname = let ts = myLLexer s in case pModule ts of
   Left err -> do
     putStrV 1 $ "Tokens:" <+> pretty ts
     throwError $ text $ fname ++ ": parse failed: " ++ err
   Right tree -> do
      let Right (rVal,rTyp) = resolveModule tree
      putStrV 1 $ "[Resolved value]" $$ pretty rVal
      putStrV 1 $ "[Resolved type]" $$ pretty rTyp
      let (res,info) = typeCheck rVal rTyp
      mapM_ (putStrV 2) info
      case res of
        Left err -> throwError err
        Right _ -> return ()

main :: IO ()
main = do
  results <- forM (files options) $ \f -> (f,) <$> (runErrorT $ runFile f)
  let oks = [f | (f, Right ()) <- results]
      errs = [(f,e) | (f, Left e) <- results]
  mapM_ (putStrLn . render . snd) errs
  putStrLn $ show (length oks) ++ "/" ++ show (length results) ++ " files typecheck."
  putStrLn $ "failing: " ++ show (map fst errs)
