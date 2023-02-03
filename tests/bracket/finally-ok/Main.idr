module Main

import Data.Swirl

import System

main : IO ()
main = do
  r <- runSwirl $ handleError die $
         withFinally' (succeed.by (putStrLn "finally") `andThen` succeed "fin res") $
           succeed.by (putStrLn "main action") `andThen` succeed "main res"
  putStrLn "swirl result: \{show r}"
