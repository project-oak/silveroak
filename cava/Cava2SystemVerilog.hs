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

module Cava2SystemVerilog
where

import qualified Cava

writeSystemVerilog :: Cava.CavaState -> IO ()
writeSystemVerilog netlist
  = writeFile (Cava.moduleName netlist ++ ".sv")
              (unlines (cava2SystemVerilog netlist))

cava2SystemVerilog :: Cava.CavaState -> [String]
cava2SystemVerilog (Cava.Coq_mkCavaState moduleName netNumber instances
                    inputs outputs)
  = ["module " ++ moduleName ++ "("] ++
    insertCommas (inputPorts inputs ++ outputPorts outputs) ++
    ["  );"]

inputPorts :: [(String, Integer)] -> [String]
inputPorts = map inputPort

inputPort :: (String, Integer) -> String
inputPort (name, _) = "  input " ++ name

outputPorts :: [(String, Integer)] -> [String]
outputPorts = map outputPort

outputPort :: (String, Integer) -> String
outputPort (name, _) = "  output " ++ name

insertCommas :: [String] -> [String]
insertCommas [] = []
insertCommas [x] = [x]
insertCommas (x:y:xs) = (x ++ ",") : insertCommas (y:xs)