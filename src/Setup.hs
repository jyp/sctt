import System.Cmd
import Distribution.Simple

main = do
  system "bnfc -d --haskell Nano.cf"
  system "bnfc -d --haskell Micro.cf"
  defaultMain
