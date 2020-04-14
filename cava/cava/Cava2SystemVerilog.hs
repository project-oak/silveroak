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

{-# LANGUAGE ViewPatterns #-}

module Cava2SystemVerilog
where

import Control.Monad.State.Lazy

import qualified BinNums
import Netlist
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
inputPort (Netlist.Coq_mkPort name (One Bit) _) = "  input logic " ++ name
inputPort (Netlist.Coq_mkPort name (One (BitVec [s])) _)
  = "  input logic[" ++ show (s - 1) ++ ":0] " ++ name

outputPorts :: [Netlist.PortDeclaration] -> [String]
outputPorts = map outputPort

outputPort :: Netlist.PortDeclaration -> String
outputPort (Netlist.Coq_mkPort name (One Bit) _) = "  output logic " ++ name
outputPort (Netlist.Coq_mkPort name (One (BitVec [s])) _)
  = "  output logic[" ++ show (s - 1) ++ ":0] " ++ name

insertCommas :: [String] -> [String]
insertCommas [] = []
insertCommas [x] = [x]
insertCommas (x:y:xs) = (x ++ ",") : insertCommas (y:xs)

data VectorDirection = HighToLow | LowToHigh
                       deriving (Eq, Show)

data VectorAssignment = AssignTo | AssignFrom

data VectorDeclaration
  = VectorDeclaration VectorAssignment Int VectorDirection [BinNums.N]

data NetlistGenerationState
  = NetlistGenerationState Int [VectorDeclaration]

computeVectors :: [Netlist.PrimitiveInstance] -> State NetlistGenerationState
                                         [String]

computeVectors instances
  = do instText <- mapM computeVectors' instances
       return instText

computeVectors' :: Netlist.PrimitiveInstance -> State NetlistGenerationState
                                        String
computeVectors' inst@(Netlist.BindPrimitive _ _ (Netlist.UnsignedAdd aSize bSize sumSize) _ _)
  | Just ((a,b),s) <- Netlist.unsignedAddercomponents inst
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
    s = length bvec
    range = case dir of
              HighToLow -> show (s - 1) ++ ":0"
              LowToHigh -> "0:" ++ show (s - 1)


populateVectors :: [VectorDeclaration] -> [String]
populateVectors = concat . map populateVector

populateVector :: VectorDeclaration -> [String]
populateVector (VectorDeclaration AssignTo v _ nets)
  = ["  assign v" ++ show v ++ "[" ++ show i ++
             "] = net[" ++ show (fromN li) ++ "];"
              | (i, li) <- zip [0..] nets]
populateVector (VectorDeclaration AssignFrom v _ nets)
  = ["  assign net[" ++ show (fromN li) ++ "] = v" ++ show v ++
             "[" ++ show i ++ "];"
             | (i, li) <- zip [0..] nets]

generateInstance :: Netlist.PrimitiveInstance -> String
generateInstance inst@(Netlist.BindPrimitive _ _ Netlist.DelayBit _ o)
  | [i] <- Netlist.instanceInputs inst
  , Just o <- Netlist.instanceNumber inst
  = "  always_ff @(posedge clk) net[" ++ show (fromN o) ++
    "] <= rst ? 1'b0 : net["
       ++ show (fromN i) ++ "];";
generateInstance inst@(Netlist.BindPrimitive _ _ Netlist.AssignBit _ _)
  | [a] <- Netlist.instanceInputs inst
  , Just b <- Netlist.instanceNumber inst
   = "  assign net[" ++ show (fromN a) ++ "] = net[" ++ show (fromN b) ++ "];"
generateInstance (Netlist.BindPrimitive _ _ (Netlist.UnsignedAdd _ _ _) ab s)
   = "" -- Generated instead during vector generation
generateInstance inst@(Netlist.BindPrimitive i o prim _ _)
  = "  " ++ instName ++ " inst" ++ show (fromN numb) ++ " " ++
    showArgs args ++ ";"
   where
   instName = maybe (error "Request for un-namable instance") id $ Netlist.primitiveName i o prim
   args = maybe (error "Primitive did not have extractable arguments!") id $ Netlist.instanceArgs inst
   numb = maybe (error "Primitive did not have an extractable instance number!") id $ Netlist.instanceNumber inst

showArgs :: [BinNums.N] -> String
showArgs args = "(" ++ concat (insertCommas (map showArg args)) ++ ")";

showArg :: BinNums.N -> String
showArg n = "net[" ++ show (fromN n) ++ "]"

wireInput :: Netlist.PortDeclaration -> [String]
wireInput port@(Netlist.Coq_mkPort name shape@(One Bit) portNets)
  | [n] <- netNumbersInPort shape portNets
  = ["  assign net[" ++ show (fromN n) ++ "] = " ++ name ++ ";"]
wireInput port@(Netlist.Coq_mkPort name shape@(One (BitVec [s])) portNets)
  | ns <- netNumbersInPort shape portNets
  = ["  assign net[" ++ show (fromN n) ++ "] = " ++ name ++ "[" ++ show i ++
     "];" |
     (n, i) <- zip ns [0..s - 1]]
wireInput (Netlist.Coq_mkPort name _ _) = error $ "Error wiring port: " ++ name

wireOutput :: Netlist.PortDeclaration -> [String]
wireOutput port@(Netlist.Coq_mkPort name shape@(One Bit) portNets)
  | [n] <- netNumbersInPort shape portNets
  = ["  assign " ++ name ++ " = net[" ++ show (fromN n) ++ "] ;"]
wireOutput port@(Netlist.Coq_mkPort name shape@(One (BitVec [s])) portNets)
  | ns <- netNumbersInPort shape portNets
  = ["  assign " ++ name ++ "[" ++ show i ++ "] = net[" ++ show (fromN n) ++
     "];" |
     (n, i) <- zip ns [0.. s - 1]]

netNumbersInPort :: Netlist.Coq_shape Coq_type -> Netlist.Coq_signalTy BinNums.N -> [BinNums.N]
netNumbersInPort shape portNets
  = case shape of
      One Bit -> [unsafeCoerce portNets :: BinNums.N]
      One (BitVec [s]) -> unsafeCoerce portNets :: [BinNums.N]
      