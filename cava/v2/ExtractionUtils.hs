{- Copyright 2019 The Project Oak Authors
  
   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at
  
       http://www.apache.org/licenses/LICENSE-2.0
  
   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-}

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
