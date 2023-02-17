module Main

import Data.Swirl.System

import System

main : IO ()
main = do
  runSwirl $ handleError (die . show) $
    handleRes (succeed.by . putStrLn . ("[ final ] Exit code: " ++) . show) $
      succeed.by . putStrLn . ("[ log ] "++) =<<: runSysCmdO ["printf", #"abc\ndef"#]
