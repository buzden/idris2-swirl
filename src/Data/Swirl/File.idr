module Data.Swirl.File

import public Data.Swirl

import public Language.Implicits.IfUnsolved

import public System.File.Error
import System.File.ReadWrite

%default covering

-- stops the swirl if it gets a file error
emitUntilEOF : HasIO io => (0 _ : IfUnsolved io IO) =>
               Alternative f => (0 _ : IfUnsolved f SnocList) =>
               (File -> io (Either e a)) ->
               File ->
               Swirl io (f e) a
emitUntilEOF act file = let _ = Prelude.MonoidAlternative in fEOF file >>= \case
  True  => done neutral
  False => emit (act file) >>= \case
    Left err => done $ pure err
    Right x => pure x ++ emitUntilEOF act file

-- stops on a file error
export
readAsChars : HasIO io => (0 _ : IfUnsolved io IO) =>
              Alternative f => (0 _ : IfUnsolved f SnocList) =>
              File ->
              Swirl io (f FileError) Char
readAsChars = emitUntilEOF fGetChar

-- stops on a file error
export
readAsLines : HasIO io => (0 _ : IfUnsolved io IO) =>
              Alternative f => (0 _ : IfUnsolved f SnocList) =>
              File ->
              Swirl io (f FileError) String
readAsLines = emitUntilEOF fGetLine

-- stops on a file error
export
writeAll : HasIO io => (0 _ : IfUnsolved io IO) =>
           Alternative f => (0 _ : IfUnsolved f SnocList) =>
           (0 _ : IfUnsolved r ()) =>
           (0 _ : IfUnsolved o Void) =>
           File ->
           Swirl io r String ->
           Swirl io (f FileError) o
writeAll file sw = let _ = Prelude.MonoidAlternative in forgetOuts $ wriggleOuts wgl $ forgetRes sw where
  wgl : String -> Swirl io (f FileError) String -> Swirl io (Swirl io (f FileError) String) String
  wgl str cont = (finish (fPutStr file str) >>= done . either (done . pure) (const cont)) @{ByResult}
