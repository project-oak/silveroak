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

module Main where

import Cava2SystemVerilog
import MixColumnsNetlist
import ShiftRowsNetlist
import SubBytesNetlist
import AddRoundKeyNetlist
import CipherControlNetlist

main :: IO ()
main = do writeSystemVerilog aes_mix_columns_Netlist
          writeTestBench aes_mix_columns_tb
          writeSystemVerilog aes_shift_rows_Netlist
          writeTestBench aes_shift_rows_tb
          writeSystemVerilog aes_sbox_lut_Netlist
          writeSystemVerilog aes_sub_bytes_Netlist
          writeTestBench aes_sub_bytes_tb
          writeSystemVerilog aes_add_round_key_Netlist
          writeTestBench aes_add_round_key_tb
          writeSystemVerilog aes_cipher_core_Netlist
