module Main

import Data.Maybe
import Data.SortedMap
import Data.String
import Data.Swirl
import Data.Swirl.File

import System
import System.File

data Nucleobase = A | C | G | T

Eq Nucleobase where
  A == A = True
  C == C = True
  G == G = True
  T == T = True
  _ == _ = False

Ord Nucleobase where
  compare = comparing $ \case
    A => 0
    C => 1
    G => 2
    T => 3

nucleoChar : Char -> Either String Nucleobase
nucleoChar 'A' = pure A
nucleoChar 'C' = pure C
nucleoChar 'G' = pure G
nucleoChar 'T' = pure T
nucleoChar k   = Left "Enexpected character: \{show k}"

showNucleobases : Show a => Monoid a => SortedMap Nucleobase a -> String
showNucleobases nbs = unwords $ nucleobases <&> show . fromMaybe neutral . flip lookup nbs where
  nucleobases : List Nucleobase
  nucleobases = [A, C, G, T]

main : IO ()
main = do
  let _ = Monoid.Additive
  r <- TailRec.result $
         writeAll' stdout $
           map ((++ "\n") . showNucleobases) $
             ToOutput.foldOuts $
               map (\k => singleton k 1) $
                 tryOrDie nucleoChar $
                   filter (/= '\n') $ filter (/= '\NUL') $
                     readAsChars stdin
  case r of
    Left fe         => die $ show fe
    Right (Left e)  => die e
    Right (Right e) => maybe (pure ()) (die . show) e
