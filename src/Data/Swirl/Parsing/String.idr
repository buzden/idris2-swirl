module Data.Swirl.Parsing.String

import Data.String.Extra
import public Data.Swirl.Parsing

%default total

export
line : RawParser m ? Void r r Char String
line = RP "" norm fin where

  norm : Char -> String -> Either String $ WhetherConsumeLast $ Swirl m Void () String
  norm '\n' str = Right $ ConsumeLast $ emit str
  norm k    str = Left $ str `strSnoc` k

  fin : String -> r -> ?
  fin str x = preEmitTo (succeed x) str
