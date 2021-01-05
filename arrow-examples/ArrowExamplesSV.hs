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

import Numeric (showHex)

import Cava2SystemVerilog
import Mux2_1
import SyntaxExamples
import UnsignedAdder
import Counter
import SignalingCounter
import Fir
-- import ArrowAdderTutorial
import D

main :: IO ()
main = do
  writeSystemVerilog adder_large_netlist
  -- writeTestBench mux2_1_tb
  -- writeSystemVerilog fullAdder_netlist
  -- writeTestBench fullAdder_tb
  -- writeSystemVerilog adder445_netlist
  -- writeTestBench adder445_tb
  -- writeSystemVerilog adder88810_netlist
  -- writeTestBench adder88810_tb
  -- writeSystemVerilog adder444_tree_4_netlist
  -- writeSystemVerilog adder444_tree_8_netlist
  -- writeSystemVerilog adder444_tree_64_netlist
  -- writeTestBench adder444_tree_4_tb
  -- writeSystemVerilog growth_tree_8_netlist
  -- writeTestBench growth_tree_8_tb
  -- writeSystemVerilog counter_3_netlist
  -- writeTestBench counter_3_tb
  -- writeSystemVerilog signaling_counter_netlist
  -- writeTestBench signaling_counter_tb
  -- writeSystemVerilog fir_netlist
  -- writeTestBench fir_tb
