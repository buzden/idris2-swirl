module Data.Swirl.Console

import public Data.Swirl

import public Language.Implicits.IfUnsolved

import System.File

%default covering

export
stdinAsChars : HasIO io =>
               Monoid r =>
               (0 _ : IfUnsolved io IO) =>
               (0 _ : IfUnsolved e Void) =>
               (0 _ : IfUnsolved r ()) =>
               Swirl io e r Char
stdinAsChars = tickUntil (fEOF @{ByResult} stdin) >> getChar

export
stdinAsLines : HasIO io =>
               Monoid r =>
               (0 _ : IfUnsolved io IO) =>
               (0 _ : IfUnsolved e Void) =>
               (0 _ : IfUnsolved r ()) =>
               Swirl io e r String
stdinAsLines = tickUntil (fEOF @{ByResult} stdin) >> getLine
