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
import Multiplexers
import FullAdderExample
import UnsignedAdderExamples
import AdderTree
import Sorter

main :: IO ()
main = do writeSystemVerilog nand2Netlist
          writeTestBench nand2_tb
          writeSystemVerilog mux2_1Netlist
          writeTestBench mux2_1_tb
          writeSystemVerilog muxBus4_8Netlist
          writeTestBench muxBus4_8_tb
          writeSystemVerilog adder4Netlist
          writeTestBench adder4_tb
          writeSystemVerilog adder8_3inputNetlist
          writeTestBench adder8_3input_tb
          writeSystemVerilog adder_tree4_8Netlist
          writeTestBench adder_tree4_8_tb
          writeSystemVerilog fullAdderNetlist
          writeTestBench fullAdder_tb
          writeSystemVerilog two_sorter_Netlist
          writeTestBench two_sorter_tb
