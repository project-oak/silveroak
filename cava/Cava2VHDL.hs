module Cava2VHDL where

import Data.List
import Control.Monad.State

import Cava
import qualified Datatypes
import ExtractionUtils

genVHDL :: String -> Coq_cava -> [String]
genVHDL name expr
  =  vhdlEntity name circuitInputs circuitOutputs ++
     vhdlArchitecture name expr
     where
     circuitInputs = findInputs expr
     circuitOutputs = findOutputs expr

writeVHDL :: String -> Coq_cava -> IO ()
writeVHDL name expr = writeFile (name ++ ".vhdl") (unlines (genVHDL name expr))

findInputs :: Coq_cava -> [String]
findInputs = nub . findInputs'

findInputs' :: Coq_cava -> [String]
findInputs' c =
  case c of
    Inv x -> findInputs' x
    And2 (Datatypes.Coq_pair i0 i1) -> findInputs' i0 ++ findInputs' i1
    Or2  (Datatypes.Coq_pair i0 i1) -> findInputs' i0 ++ findInputs' i1
    Delay x -> findInputs' x
    Signal name -> [decodeCoqString name]
    Output _ expr -> findInputs' expr

findOutputs :: Coq_cava -> [String]
findOutputs = nub . findOutputs'
    
findOutputs' :: Coq_cava -> [String]
findOutputs' c =
  case c of
    Inv x -> findOutputs' x
    And2 (Datatypes.Coq_pair i0 i1) -> findOutputs' i0 ++ findOutputs' i1
    Or2  (Datatypes.Coq_pair i0 i1) -> findOutputs' i0 ++ findOutputs' i1
    Delay x -> findInputs' x
    Signal _ -> []
    Output name _ -> [decodeCoqString name]

vhdlEntity :: String -> [String] -> [String] -> [String]
vhdlEntity name inputs outputs
  = ["entity " ++ name ++ " is",
      "  port("] ++
    insertSemicolons (map vhdlInput inputs ++ map vhdlOutput outputs) ++
    [
      "  );",
      "end entity " ++ name ++ ";"
    ]

vhdlArchitecture :: String -> Cava.Coq_cava -> [String]
vhdlArchitecture name expr
  = ["use work.cava.all;",
     "architecture cava of " ++ name ++ " is",
     "begin"] ++
     snd instances ++
    ["end architecture cava ;"
    ]
    where
    (_, instances) = runState (vhdlInstantiation expr) (0, [])

vhdlInput :: String -> String
vhdlInput name = "    signal " ++ name ++ " : in bit"

vhdlOutput :: String -> String
vhdlOutput name = "    signal " ++ name ++ " : out bit"

insertSemicolons :: [String] -> [String]
insertSemicolons [] = []
insertSemicolons [x] = [x]
insertSemicolons (x:xs) = (x ++ ";") : insertSemicolons xs

insertCommas :: [String] -> [String]
insertCommas [] = []
insertCommas [x] = [x]
insertCommas (x:xs) = (x ++ ",") : insertCommas xs

type NetlistState = (Int, [String])


vhdlOpWithPortNames :: String -> [Cava.Coq_cava] -> [String] ->
                       State NetlistState Int
vhdlOpWithPortNames name inputs portNames
  = do instantiatedInputs <- mapM vhdlInstantiation inputs
       (o, netlist) <- get
       let inputPorts = zipWith wireUpPort (init portNames) instantiatedInputs
           allPorts = inputPorts ++ [wireUpPort (last portNames) o]
           inst = "  " ++ name ++ "_" ++ show o ++
                  " : " ++ name ++ " port map (\n" ++
                  unlines (insertCommas allPorts) ++ "  );"
       put (o+1, inst:netlist)
       return o
    where
    wireUpPort name i = "    " ++ name ++ " => net(" ++ show i ++ ")"


vhdlUnaryOp :: String -> Cava.Coq_cava ->
               State NetlistState Int
vhdlUnaryOp name i = vhdlOpWithPortNames name [i] ["i", "o"]

vhdlBinaryOp :: String ->
                Datatypes.Coq_prod Cava.Coq_cava Cava.Coq_cava ->
                State NetlistState Int
vhdlBinaryOp name (Datatypes.Coq_pair i0 i1)
  = vhdlOpWithPortNames name [i0, i1] ["i0", "i1", "o"]

vhdlInstantiation :: Coq_cava -> State NetlistState Int
vhdlInstantiation (Inv x) = vhdlUnaryOp "inv" x
vhdlInstantiation (And2 inputs) = vhdlBinaryOp "and2" inputs
vhdlInstantiation (Or2 inputs)  = vhdlBinaryOp "or2" inputs
vhdlInstantiation (Signal name)
  = do (o, netlist) <- get
       let assignment = "  net(" ++ show o ++ ") <= " ++ (decodeCoqString name)
                        ++ ";"
       put (o+1, assignment:netlist)
       return o
vhdlInstantiation (Output name expr)
       = do expri <- vhdlInstantiation expr
            (o, netlist) <- get
            let assignment = "  " ++ decodeCoqString name ++ " <= net(" ++
                             show expri ++ ");";
            put (o, assignment:netlist)
            return o      