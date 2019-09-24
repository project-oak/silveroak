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

main ::IO ()
main
  = do putStrLn ("Inputs:  " ++ show circuitInputs)
       putStrLn ("Outputs: " ++ show circuitOutputs)
       putStrLn (unlines entity)