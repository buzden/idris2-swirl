module Data.Swirl.System

import Data.String
import public Data.Swirl
import Data.Swirl.File

import public Language.Implicits.IfUnsolved

import System.File
import public System.File.Error

%default covering

||| Run a system command emitting lines that are printed to its standard output
||| and returning exit code as the result value.
||| Lines except the last one would have the newline at the end.
export
runSysCmdOLn : HasIO io => (cmd : List String) -> Swirl io FileError Int String
runSysCmdOLn cmd = mapFst fst $ bracket'
  (succeedOrFail.by $ popen cmd Read)
  (succeed.by . pclose)
  readAsLines

trimRLn : String -> String
trimRLn str = do
  let S n = length str
    | Z => ""
  if assert_total $ strIndex str (cast n) == '\n'
    then substr 0 n str
    else str

||| Run a system command emitting lines that are printed to its standard output
||| and returning exit code as the result value.
||| Lines do not have a trailing newline and information of whether the last line had it is lost.
export
runSysCmdO : HasIO io => (cmd : List String) -> Swirl io FileError Int String
runSysCmdO = map trimRLn . filter (/= "") . runSysCmdOLn

||| Run a system command being fed a stream of input strings
||| and returning exit code (along with the feeding stream result).
export total
runSysCmdI : HasIO io => (cmd : List String) -> Swirl io e r String -> Swirl io (Either e FileError) (r, Int) Void
runSysCmdI cmd sw = mapFst swap $ bracket'
  (mapError Right $ succeedOrFail.by $ popen cmd WriteTruncate)
  (succeed.by . pclose)
  $ \inF => squashOuts' $ sw <&> succeedOrFail.by . fPutStr inF

export total
runSysCmdILn : HasIO io => (cmd : List String) -> Swirl io e r String -> Swirl io (Either e FileError) (r, Int) Void
runSysCmdILn cmd = runSysCmdI cmd . map (++ "\n")
