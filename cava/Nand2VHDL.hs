module Main
where

import Nand2
import Cava2VHDL

circuitInputs :: [String]
circuitInputs = findInputs and2Alt_top

main ::IO ()
main
  = putStrLn (show circuitInputs)