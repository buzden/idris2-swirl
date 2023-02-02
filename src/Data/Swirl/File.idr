module Data.Swirl.File

import public Data.Swirl

import public Language.Implicits.IfUnsolved

import System.File
import public System.File.Error
import public System.File.Mode

%default covering

emitUntilEOF : HasIO io =>
               Monoid r =>
               (0 _ : IfUnsolved io IO) =>
               (0 _ : IfUnsolved r ()) =>
               (File -> io (Either e a)) ->
               File ->
               Swirl io e r a
emitUntilEOF act file = fEOF file >>= \case
  True  => succeed neutral
  False => emit.by (act file) >>= \case
    Left err => fail err
    Right x => pure x ++ emitUntilEOF act file

export
readAsChars : HasIO io =>
              Monoid r =>
              (0 _ : IfUnsolved io IO) =>
              (0 _ : IfUnsolved r ()) =>
              File ->
              Swirl io FileError r Char
readAsChars = emitUntilEOF fGetChar

export
readAsLines : HasIO io =>
              Monoid r =>
              (0 _ : IfUnsolved io IO) =>
              (0 _ : IfUnsolved r ()) =>
              File ->
              Swirl io FileError r String
readAsLines = emitUntilEOF fGetLine

export
readAsChunks : HasIO io =>
               Monoid r =>
               (0 _ : IfUnsolved io IO) =>
               (0 _ : IfUnsolved r ()) =>
               (chunkMaxSize : Nat) ->
               File ->
               Swirl io FileError r String
readAsChunks sz = emitUntilEOF $ \file => fGetChars file $ cast sz

export
writeStr : HasIO io =>
           Monoid r =>
           (0 _ : IfUnsolved io IO) =>
           (0 _ : IfUnsolved r ()) =>
           (0 _ : IfUnsolved o Void) =>
           File ->
           String ->
           Swirl io FileError r o
writeStr file str = mapFst (const neutral) $ succeedOrFail.by $ fPutStr file str

export
withFile : HasIO io =>
           (mode : Mode) ->
           (filename : String) ->
           (File -> Swirl io FileError r o) ->
           Swirl io FileError r o
withFile mode filename = bracket (succeedOrFail.by $ openFile filename mode) (succeed.by . closeFile)

export
withFile' : HasIO io =>
            (mode : Mode) ->
            (filename : String) ->
            (File -> Swirl io (Either FileError e) r o) ->
            Swirl io (Either FileError e) r o
withFile' mode filename = bracket (mapError Left $ succeedOrFail.by $ openFile filename mode) (succeed.by . closeFile)
