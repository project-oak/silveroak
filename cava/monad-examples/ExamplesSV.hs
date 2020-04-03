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
import NandGate
import FullAdder
import UnsignedAdder
import AdderTree

main :: IO ()
main = do writeSystemVerilog nand2Netlist
          writeSystemVerilog fullAdderNetlist
          writeSystemVerilog fullAdderFCNetlist
          writeSystemVerilog adder8Netlist
          writeSystemVerilog adder8_3inNetlist
          writeSystemVerilog adder_fixedNetlist
          writeSystemVerilog adder_tree_4_8Netlist
          writeSystemVerilog pipelinedNANDNetlist
