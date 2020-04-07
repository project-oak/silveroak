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

module Cava2SystemVerilog
where

import Control.Monad.State.Lazy

import qualified BinNums
import qualified Netlist
import qualified Vector

writeSystemVerilog :: Netlist.CavaState -> IO ()
writeSystemVerilog cavastate
  = writeFile (Netlist.moduleName (Netlist.coq_module cavastate) ++ ".sv")
              (unlines (cava2SystemVerilog cavastate))

fromN :: BinNums.N -> Integer
fromN bn
  = case bn of
      BinNums.N0 -> 0
      BinNums.Npos n -> n

cava2SystemVerilog :: Netlist.CavaState -> [String]
cava2SystemVerilog (Netlist.Coq_mkCavaState netNumber isSeq (Netlist.Coq_mkModule moduleName instances
                    inputs outputs))
  = ["module " ++ moduleName ++ "("] ++

    insertCommas (clockPorts ++ inputPorts inputs ++ outputPorts outputs) ++
    ["  );"] ++
    ["",
     "  timeunit 1ns; timeprecision 1ns;",
     ""] ++
    ["  logic[" ++ show (fromN netNumber-1) ++ ":0] net;"] ++
    declareVectors vDefs ++
    [""] ++
    ["  // Constant nets",
     "  assign net[0] = 1'b0;",
     "  assign net[1] = 1'b1;",
     "  // Wire up inputs."] ++
    concat (map wireInput inputs) ++
    ["  // Wire up outputs."] ++
    concat (map wireOutput outputs) ++
    ["  // Populate vectors."] ++
    populateVectors vDefs ++
    [""] ++
    instText ++
    [""] ++
    ["endmodule"]
    where
    clockPorts = if isSeq then
                   ["  input logic clk",
                    "  input logic rst"]
                 else
                   []
    (instText, NetlistGenerationState v vDefs)
      = runState (computeVectors instances) (NetlistGenerationState 0 [])

inputPorts :: [Netlist.PortDeclaration] -> [String]
inputPorts = map inputPort

inputPort :: Netlist.PortDeclaration -> String
inputPort (Netlist.Coq_mkPort name (Netlist.BitPort _)) = "  input logic " ++ name
inputPort (Netlist.Coq_mkPort name (Netlist.VectorTo0Port s v))
  = "  input logic[" ++ show (s - 1) ++ ":0] " ++ name
inputPort (Netlist.Coq_mkPort name (Netlist.VectorFrom0Port s v))
  = "  input logic[0:" ++ show (s - 1) ++ "] " ++ name

outputPorts :: [Netlist.PortDeclaration] -> [String]
outputPorts = map outputPort

outputPort :: Netlist.PortDeclaration -> String
outputPort (Netlist.Coq_mkPort name (Netlist.BitPort _)) = "  output logic " ++ name
outputPort (Netlist.Coq_mkPort name (Netlist.VectorTo0Port s v))
  = "  output logic[" ++ show (s - 1) ++ ":0] " ++ name
outputPort (Netlist.Coq_mkPort name (Netlist.VectorFrom0Port s v))
  = "  output logic[0:" ++ show (s - 1) ++ "] " ++ name

insertCommas :: [String] -> [String]
insertCommas [] = []
insertCommas [x] = [x]
insertCommas (x:y:xs) = (x ++ ",") : insertCommas (y:xs)

data VectorDirection = HighToLow | LowToHigh
                       deriving (Eq, Show)

data VectorAssignment = AssignTo | AssignFrom                      

data VectorDeclaration
  = VectorDeclaration VectorAssignment Int VectorDirection
                      (Vector.Coq_t BinNums.N)

data NetlistGenerationState
  = NetlistGenerationState Int [VectorDeclaration] 

computeVectors :: [Netlist.Primitive] -> State NetlistGenerationState
                                         [String]

computeVectors instances
  = do instText <- mapM computeVectors' instances
       return instText

computeVectors' :: Netlist.Primitive -> State NetlistGenerationState
                                        String
computeVectors' (Netlist.UnsignedAdd aSize bSize sumSize a b s)
  = do NetlistGenerationState v vDecs <- get
       let vA = VectorDeclaration AssignTo   v       HighToLow a
           vB = VectorDeclaration AssignTo   (v + 1) HighToLow b
           vC = VectorDeclaration AssignFrom (v + 2) HighToLow s
       put (NetlistGenerationState (v + 3) (vA:vB:vC:vDecs))
       return ("  assign v" ++ show (v + 2) ++ " = v" ++ show v ++
               " + v" ++ show (v + 1) ++ ";")                                       
computeVectors' otherInst = return (generateInstance otherInst)

declareVectors :: [VectorDeclaration] -> [String]
declareVectors = map declareVector

vecLength :: Vector.Coq_t a -> Integer
vecLength v
  = case v of
      Vector.Coq_nil -> 0
      Vector.Coq_cons _ n _ -> n


vecToList :: Vector.Coq_t a -> [a]
vecToList v = Vector.to_list (vecLength v) v

declareVector :: VectorDeclaration -> String
declareVector (VectorDeclaration _ i dir bvec)
  = "  logic[" ++ range ++ "] v" ++ show i ++ ";"
    where
    s = length (vecToList bvec)
    range = case dir of
              HighToLow -> show (s - 1) ++ ":0"
              LowToHigh -> "0:" ++ show (s - 1)


populateVectors :: [VectorDeclaration] -> [String]
populateVectors = concat . map populateVector

populateVector :: VectorDeclaration -> [String]
populateVector (VectorDeclaration AssignTo v _ nets)
  = ["  assign v" ++ show v ++ "[" ++ show i ++
             "] = net[" ++ show (fromN li) ++ "];"
              | (i, li) <- zip [0..] (vecToList nets)]
populateVector (VectorDeclaration AssignFrom v _ nets)
  = ["  assign net[" ++ show (fromN li) ++ "] = v" ++ show v ++
             "[" ++ show i ++ "];"
             | (i, li) <- zip [0..] (vecToList nets)]

nameOfInstance :: Netlist.Primitive -> String
nameOfInstance inst
  = case inst of
      Netlist.Not _ _ -> "not"
      Netlist.And _ _ -> "and"
      Netlist.Nand _ _ -> "nand"
      Netlist.Or _ _ -> "or"
      Netlist.Nor _ _ -> "nor"
      Netlist.Xor _ _-> "xor"
      Netlist.Xnor _ _ -> "xnor"
      Netlist.Buf _ _ -> "buf"
      Netlist.Xorcy _ _ _ -> "XORCY"
      Netlist.Muxcy _ _ _ _ -> "MUXCY"
      _ -> error "Request for un-namable instance"

instanceArgs :: Netlist.Primitive -> [BinNums.N]
instanceArgs inst
  = case inst of
      Netlist.Not i o -> [o, i]
      Netlist.And i o -> o:i
      Netlist.Nand i o -> o:i
      Netlist.Or i o -> o:i
      Netlist.Nor i o -> o:i
      Netlist.Xor i o -> o:i
      Netlist.Xnor i o -> o:i
      Netlist.Buf i o -> [o, i]
      Netlist.Xorcy li ci o -> [o, ci, li]
      Netlist.Muxcy s di ci o -> [o, ci, di, s]
      _ -> error "Request for bad instance arguments"

instanceNumber :: Netlist.Primitive -> BinNums.N
instanceNumber inst
  = case inst of
      Netlist.Not _ o -> o
      Netlist.And _ o -> o
      Netlist.Nand _ o -> o
      Netlist.Or _ o -> o
      Netlist.Nor _ o -> o
      Netlist.Xor _ o -> o
      Netlist.Xnor _ o -> o
      Netlist.Buf _ o -> o
      Netlist.Xorcy _ _ o -> o
      Netlist.Muxcy _ _ _ o -> o
      _ -> error "Request for bad instance number"

generateInstance :: Netlist.Primitive -> String
generateInstance (Netlist.DelayBit i o)
   = "  always_ff @(posedge clk) net[" ++ show (fromN o) ++
     "] <= rst ? 1'b0 : net["
        ++ show (fromN i) ++ "];";
generateInstance (Netlist.AssignBit a b)
   = "  assign net[" ++ show (fromN a) ++ "] = net[" ++ show (fromN b) ++ "];"
generateInstance (Netlist.UnsignedAdd _ _ _ _ _ _)
   = "" -- Generated instead during vector generation
generateInstance inst
  = "  " ++ instName ++ " inst" ++ show (fromN numb) ++ " " ++
    showArgs args ++ ";"
   where
   instName = nameOfInstance inst
   args = instanceArgs inst
   numb = instanceNumber inst

showArgs :: [BinNums.N] -> String
showArgs args = "(" ++ concat (insertCommas (map showArg args)) ++ ")";

showArg :: BinNums.N -> String
showArg n = "net[" ++ show (fromN n) ++ "]"

wireInput :: Netlist.PortDeclaration -> [String]
wireInput (Netlist.Coq_mkPort name (Netlist.BitPort n))
  = ["  assign net[" ++ show (fromN n) ++ "] = " ++ name ++ ";"]
wireInput (Netlist.Coq_mkPort name (Netlist.VectorTo0Port s v))
  = ["  assign net[" ++ show (fromN n) ++ "] = " ++ name ++ "[" ++ show i ++
     "];" |
     (n, i) <- zip (Vector.to_list s v) [0..s - 1]]

wireOutput :: Netlist.PortDeclaration -> [String]
wireOutput (Netlist.Coq_mkPort name (Netlist.BitPort n))
  = ["  assign " ++ name ++ " = net[" ++ show (fromN n) ++ "] ;"]
wireOutput (Netlist.Coq_mkPort name (Netlist.VectorTo0Port s v))
  = ["  assign " ++ name ++ "[" ++ show i ++ "] = net[" ++ show (fromN n) ++
     "];" |
     (n, i) <- zip (Vector.to_list s v) [0.. s - 1]]
