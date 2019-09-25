module Main
where

import Nand2
import Cava2VHDL

circuitInputs :: [String]
circuitInputs = findInputs and2Alt_top

circuitOutputs :: [String]
circuitOutputs = findOutputs and2Alt_top

entity :: [String]
entity = vhdlEntity "nand2" circuitInputs circuitOutputs

architecture :: [String]
architecture = vhdlArchitecture "nand2_gate" and2Alt_top

main ::IO ()
main
  = writeVHDL "nand2_gate" and2Alt_top