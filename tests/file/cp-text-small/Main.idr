module Main

import Data.Swirl
import Data.Swirl.File

import System
import System.File

main : IO ()
main = do
  Right xx <- result $
                withFile Read "from" $ \from =>
                  withFile WriteTruncate "to" $ \to =>
                    readAsChunks 1024 from >>= writeStr to
  | Left err => die $ show err
  pure xx
