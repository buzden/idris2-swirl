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

export
fileAsChars : HasIO io => (0 _ : IfUnsolved io IO) =>
              Alternative f => (0 _ : IfUnsolved f SnocList) =>
              File ->
              Swirl io (f FileError) Char
fileAsChars = emitUntilEOF fGetChar

export
fileAsLines : HasIO io => (0 _ : IfUnsolved io IO) =>
              Alternative f => (0 _ : IfUnsolved f SnocList) =>
              File ->
              Swirl io (f FileError) String
fileAsLines = emitUntilEOF fGetLine
