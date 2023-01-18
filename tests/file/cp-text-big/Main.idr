module Main

import Data.Swirl
import Data.Swirl.File

import System
import System.File

main : IO ()
main = do
  Right () <- withFile "from" Read (die . show) $ \from =>
                withFile "to" WriteTruncate (die . show) $ \to => do
                  res <- TailRec.result $ writeAll' to $ readAsChunks (1024 * 1023) from
                  pure $ case res of
                    Left err => Left err
                    Right x => case the (Maybe FileError) x of
                      Nothing  => Right ()
                      Just err => Left err
    | Left err => die $ show err
  pure ()
