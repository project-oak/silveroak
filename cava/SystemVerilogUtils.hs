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

module SystemVerilogUtils
where

import Signal

insertCommas :: [String] -> [String]
insertCommas [] = []
insertCommas [x] = [x]
insertCommas (x:y:xs) = (x ++ ",") : insertCommas (y:xs)

vectorDeclaration' ::  SignalType -> Integer -> String
vectorDeclaration' k s
  = case k of
      Bit -> "[" ++ show (s - 1) ++ ":0]"
      Vec k2 s2 -> "[" ++ show (s - 1) ++ ":0]" ++  vectorDeclaration' k2 s2

vectorDeclaration :: String -> SignalType -> Integer -> String
vectorDeclaration name k s
  = "logic " ++ vectorDeclaration' k s ++ name

declareSignal :: String -> SignalType -> String
declareSignal name typ
  = case typ of
      Bit -> "logic " ++ name
      Vec t s -> vectorDeclaration name t s
      ExternalType typeName ->  typeName ++ " " ++ name
