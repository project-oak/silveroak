module Cava2VHDL where
import Cava
import qualified Datatypes

findInputs' :: Coq_cava -> [String]
findInputs' c =
  case c of
    Inv x -> findInputs x
    And2 (Datatypes.Coq_prod i0 i1) -> findInputs i0 ++ findInputs i1
    Or2  (Datatypes.Coq_prod i0 i1) -> findInputs i0 ++ findInputs i1
    Delay x -> findInpiuts x
    Signal name -> [name]
    Output _ name -> [name]
