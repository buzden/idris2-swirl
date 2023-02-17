module Data.Swirl.System

import public Data.Swirl
import Data.Swirl.File

import public Language.Implicits.IfUnsolved

import System.File
import public System.File.Error

%default total

||| Run a system command emitting lines that are printed to its standard output
||| and returning exit code as the result value.
export covering
runSysCmd : HasIO io => (cmd : List String) -> Swirl io FileError Int String
runSysCmd cmd = mapFst fst $ bracket'
  (succeedOrFail.by $ popen cmd Read)
  (succeed.by . pclose)
  readAsLines
