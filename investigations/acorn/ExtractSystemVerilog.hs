{- Copyright 2021 The Project Oak Authors

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

import Control.Monad
import System.Environment

main :: IO ()
main
  = do args <- getArgs
       when (length args /= 1) $ error ("Expect exactly one filename argument, got: " ++ show args)
       let filename = head args
       contents <- readFile (filename++ ".out")
       writeFile filename (recoverNewlines (extractString contents))

extractString :: String -> String
extractString s
  = (takeWhile ((/=)'"') afterFirstQuote)
  where
  afterFirstQuote = tail (dropWhile ((/=)'"') s)

recoverNewlines :: String -> String
recoverNewlines "" = "\n"
recoverNewlines ('\\':'n':xs) = '\n' : recoverNewlines xs
recoverNewlines (x:xs) = x : recoverNewlines xs