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
import XilinxAdder
import XilinxAdderExamples
import XilinxAdderTree

main :: IO ()
main = do writeSystemVerilog adder8Netlist
          writeTestBench adder8_tb
          writeSystemVerilog adder_tree4_8Netlist
          writeTestBench adder_tree4_8_tb
          writeSystemVerilog adder_tree32_8Netlist
          writeSystemVerilog adder_tree64_8Netlist
          writeTestBench adder_tree64_8_tb
          writeTestBench adder_tree64_128_tb
          writeSystemVerilog adder_tree64_128Netlist
          -- writeSystemVerilog adder_tree128_256Netlist
          -- writeTestBench adder_tree128_256_tb

