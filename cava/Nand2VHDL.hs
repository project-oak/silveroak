module Main
where

import Nand2
import Cava2VHDL

main ::IO ()
main
  = writeVHDL "nand2_gate" and2_pipelined_top