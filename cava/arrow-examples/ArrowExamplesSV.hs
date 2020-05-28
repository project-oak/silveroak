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
import Mux2_1
import Examples
import SyntaxExamples

main :: IO ()
main = do writeSystemVerilog nandArrow
          writeTestBench arrow_nand2_tb
          writeSystemVerilog xorArrow
          writeTestBench arrow_xor_tb
          writeSystemVerilog feedbackNandArrow
          writeTestBench feedbackNandArrow_tb
          writeSystemVerilog mux2_1_netlist
          writeTestBench mux2_1_tb
