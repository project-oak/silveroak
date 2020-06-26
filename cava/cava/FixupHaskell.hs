{- Copyright 2020 The Project Oak Authors
  
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

module Main
where

fixup :: String -> String
fixup content
  = unlines updatedLines
    where
    contentLines = lines content
    updatedLines = take 3 contentLines ++
                   extraImports ++
                   drop 3 contentLines
    extraImports = ["import qualified Data.Bits",
                    "import qualified Data.Char"]

main :: IO ()
main
  = do asciiContent <- readFile "Ascii.hs"
       writeFile "Ascii2.hs" (fixup asciiContent)
       bytevectorContent <- readFile "ByteVector.hs"
       writeFile "ByteVector2.hs" (fixup bytevectorContent)
       -- decimalStringContent <- readFile "DecimalString.hs"
       -- writeFile "DecimalString2.hs" (fixup decimalStringContent)
