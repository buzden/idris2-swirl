module Main

import Data.Either

import Data.Swirl.System

import System

main : IO ()
main = do
  runSwirl $ handleError (die . show) $
    handleRes (succeed.by . putStrLn . ("[ final ] Result: " ++) . show) $
      runSysCmdILn ["./cmd"] $
        emit "first line" `andThen` emit "second line" `andThen` succeed 'k'
