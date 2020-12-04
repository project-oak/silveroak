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


module Main where

import Cava2SystemVerilog
import Instantiate
import TestMultiply
import Delay

main :: IO ()
main = do writeSystemVerilog instantiateNetlist
          writeTestBench instantiate_tb
          writeSystemVerilog mult2_3_5Netlist
          writeTestBench mult2_3_5_tb
          writeSystemVerilog delayByte_Netlist
          writeTestBench delayByte_tb
          writeSystemVerilog pipelinedNANDNetlist
          -- writeTestBench pipelinedNAND_tb
