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

import AccumulatingAdderEnable
import Cava2SystemVerilog
import Instantiate
import MuxTests
import TestMultiply
import Delay
import CountBy
import DoubleCountBy
import Array
import TestVecConstEq
import TestDecoder

main :: IO ()
main = do writeSystemVerilog mux2_1Netlist
          writeTestBench mux2_1_tb
          writeSystemVerilog muxBus4_8Netlist
          writeTestBench muxBus4_8_tb
          writeSystemVerilog instantiateNetlist
          writeTestBench instantiate_tb
          writeSystemVerilog mult2_3_5Netlist
          writeTestBench mult2_3_5_tb
          writeSystemVerilog delayByte_Netlist
          writeTestBench delayByte_tb
          writeSystemVerilog delayEnableByte_Netlist
          writeTestBench delayEnableByte_tb
          writeSystemVerilog pipelinedNANDNetlist
          -- writeTestBench pipelinedNAND_tb
          writeSystemVerilog countBy_Netlist
          writeTestBench countBy_tb
          writeSystemVerilog double_count_by_Netlist
          writeTestBench double_count_by_tb
          writeSystemVerilog accumulatingAdderEnable_Netlist
          writeSystemVerilog arrayTest_Netlist
          writeTestBench arrayTest_tb
          writeSystemVerilog multiDimArrayTest_Netlist
          writeTestBench multiDimArrayTest_tb
          writeSystemVerilog vecConstEq8_42Netlist
          writeTestBench vecConstEq8_42_tb
          writeSystemVerilog decoder2Netlist
          writeTestBench decoder2_tb
          writeSystemVerilog encoder2Netlist
          writeTestBench encoder2_tb
          writeSystemVerilog encoderdecoderNetlist
          writeTestBench encoderdecoder_tb
