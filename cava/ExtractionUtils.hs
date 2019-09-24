module ExtractionUtils
where

import Data.Char(chr)

import qualified Ascii
import qualified Datatypes
import String

decodeList :: Datatypes.Coq_list a -> [a]
decodeList Datatypes.Coq_nil = []
decodeList (Datatypes.Coq_cons x xs) = x : decodeList xs

decodeCoqString :: Coq_string -> String
decodeCoqString String.EmptyString = []
decodeCoqString (String coqChar rest)
  = decodeCoqChar coqChar : decodeCoqString rest

decodeCoqChar :: Ascii.Coq_ascii -> Char
decodeCoqChar (Ascii.Ascii b7 b6 b5 b4 b3 b2 b1 b0)
  = chr (sum (zipWith (*) charBits powersOf2))
    where
    charBits :: [Int]
    charBits = map bool2Int (reverse [b7, b6, b5, b4, b3, b2, b1, b0])
    bool2Int :: Datatypes.Coq_bool -> Int
    bool2Int Datatypes.Coq_false = 0
    bool2Int Datatypes.Coq_true = 1
    powersOf2 :: [Int]
    powersOf2 = [2^n | n <- reverse [0..7]]
