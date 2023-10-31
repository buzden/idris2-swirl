module Main

import Data.Swirl.Parsing.String
import Data.Swirl.File

import System
import System.File

originalText : String
originalText = """
  A multi-line text
  =================

  This is a multi-line text.
  It has a markdown-like header
  and several lines afterwards
  """

originalSwirl : Swirl m Double () Char
originalSwirl = emits' $ fastUnpack originalText

errorText : String
errorText = """
  This is an additional text
  emitted by the error's handler

  """

errorHandler : Double -> Swirl m Void () Char
errorHandler _ = emits' $ fastUnpack errorText

main : IO ()
main = do
  runSwirl $ handleError (die . show) $
    writeStr stdout . (\s => "[ a line ] \{s}\n") =<<
      (mapError absurd $ rawParseAll line $ handleError errorHandler originalSwirl)
