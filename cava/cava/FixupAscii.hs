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

module Main
where

main :: IO ()
main
  = do content <- readFile "Ascii.hs"
       let contentLines = lines content
           updatedLines = take 2 contentLines ++
                          extraImports ++
                          drop 2 contentLines
       writeFile "Ascii2.hs" (unlines updatedLines)
    where
    extraImports = ["import qualified Data.Bits",
                    "import qualified Data.Char"]