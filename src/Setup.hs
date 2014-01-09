import System.Cmd
import Distribution.Simple

main = do
  system "bnfc -d Nano.cf"
  system "bnfc -d Micro.cf"
  defaultMain
