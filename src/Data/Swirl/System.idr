module Data.Swirl.System

import public Data.Swirl
import Data.Swirl.File

import public Language.Implicits.IfUnsolved

import System.File
import public System.File.Error

%default covering

||| Run a system command emitting lines that are printed to its standard output
||| and returning exit code as the result value.
export
runSysCmdO : HasIO io => (cmd : List String) -> Swirl io FileError Int String
runSysCmdO cmd = mapFst fst $ bracket'
  (succeedOrFail.by $ popen cmd Read)
  (succeed.by . pclose)
  readAsLines

||| Run a system command being fed a stream of input strings
||| and returning exit code (along with the feeding stream result).
export
runSysCmdI : HasIO io => (cmd : List String) -> Swirl io e r String -> Swirl io (Either e FileError) (r, Int) Void
runSysCmdI cmd sw = mapFst swap $ bracket'
  (mapError Right $ succeedOrFail.by $ popen cmd WriteTruncate)
  (succeed.by . pclose)
  $ \inF => squashOuts' $ sw <&> succeedOrFail.by . fPutStr inF

export
runSysCmdILn : HasIO io => (cmd : List String) -> Swirl io e r String -> Swirl io (Either e FileError) (r, Int) Void
runSysCmdILn cmd = runSysCmdI cmd . map (++ "\n")
