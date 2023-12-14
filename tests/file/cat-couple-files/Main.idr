module Main

import Data.Swirl
import Data.Swirl.File
import Data.Swirl.Console

import System
import System.File.Virtual

main : IO ()
main = do
  (_::args) <- getArgs | [] => pure ()
  runSwirl $ emits' args >>= \input =>
    handleError (die . ("Error at file \{input}: " ++) . show) $
      withFile Read input $
        readAsChunks (1024 * 1023) >=> writeStr stdout
