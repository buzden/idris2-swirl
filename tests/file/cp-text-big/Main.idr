module Main

import Data.Swirl
import Data.Swirl.File

import System

main : IO ()
main =
  runSwirl $ handleError (die . show) $
    withFile Read "from" $ \from =>
      withFile WriteTruncate "to" $ \to =>
        readAsChunks (1024 * 1023) from >>= writeStr to
