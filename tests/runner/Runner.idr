module Runner

import BaseDir

import Test.Golden.RunnerHelper

RunScriptArg where
  runScriptArg = baseTestsDir ++ "/.pack_lock"

main : IO ()
main = goldenRunner
  [ "Documentation" `atDir` "docs"
  , "File API" `atDir` "file"
  , "Console API" `atDir` "console"
  , "Finalising and bracketing" `atDir` "bracket"
  , "Running system commands" `atDir` "system"
  ]
