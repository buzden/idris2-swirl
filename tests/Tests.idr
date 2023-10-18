module Tests

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner
  [ "Documentation" `atDir` "docs"
  , "File API" `atDir` "file"
  , "Console API" `atDir` "console"
  , "Finalising and bracketing" `atDir` "bracket"
  , "Running system commands" `atDir` "system"
  ]
