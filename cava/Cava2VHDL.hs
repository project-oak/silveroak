module Cava2VHDL where
import Nand2Alt

findInputs' :: Cava -> [String]
findInputs' c =
  case c of
    Inv x -> findInputs x
    And2 (Prod i0 i1) -> findInputs i0 ++ findInputs i1
    Or2  (Prod i0 i1) -> findInputs i0 ++ findInputs i1
    Delay x -> findInpiuts x
    Signal name -> [name]
    Output _ name -> [name]
