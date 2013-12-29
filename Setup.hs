import System.Cmd
import Distribution.Simple

main = do
  system "bnfc -d Nano.cf"
  defaultMain
