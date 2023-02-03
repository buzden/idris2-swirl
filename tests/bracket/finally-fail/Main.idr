module Main

import Data.Swirl

import System
import System.File

putStrLn' : HasIO io => String -> io ()
putStrLn' str = putStrLn str >> fflush stdout

main : IO ()
main = do
  r <- runSwirl $ handleError die $
         withFinally' (succeed.by (putStrLn' "finally") `andThen` succeed "fin res") $
           succeed.by (putStrLn' "main action") `andThen` fail "main fail"
  putStrLn "swirl result: \{show r}"
