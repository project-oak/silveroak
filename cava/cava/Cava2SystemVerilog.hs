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

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Cava2SystemVerilog
where

import Control.Monad.State.Lazy

import qualified BinNums
import Netlist
import qualified Vector

writeSystemVerilog :: Netlist.CavaState -> IO ()
writeSystemVerilog cavastate
  = do putStr ("Generating " ++ filename ++ "...")
       writeFile filename (unlines (cava2SystemVerilog cavastate))
       putStrLn (" [done]")
    where
    filename = Netlist.moduleName (Netlist.coq_module cavastate) ++ ".sv"

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
     "  assign net[1] = 1'b1;"] ++
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
inputPort (Netlist.Coq_mkPort name Bit) = "  input logic " ++ name
inputPort (Netlist.Coq_mkPort name (BitVec [s]))
  = "  input logic[" ++ show (s - 1) ++ ":0] " ++ name

outputPorts :: [Netlist.PortDeclaration] -> [String]
outputPorts = map outputPort

outputPort :: Netlist.PortDeclaration -> String
outputPort (Netlist.Coq_mkPort name Bit) = "  output logic " ++ name
outputPort (Netlist.Coq_mkPort name (BitVec [s]))
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

computeVectors :: [Netlist.PrimitiveInstance] ->
                   State NetlistGenerationState [String]

computeVectors instances
  = do instText <- mapM computeVectors' (zip instances [1..])
       return instText

computeVectors' :: (Netlist.PrimitiveInstance, Int) ->
                   State NetlistGenerationState String
computeVectors' (inst@(Netlist.BindPrimitive _ _ (Netlist.UnsignedAdd aSize bSize sumSize) _ _), _)
  | Just ((a,b),s) <- Netlist.unsignedAddercomponents inst
  = do NetlistGenerationState v vDecs <- get
       let vA = VectorDeclaration AssignTo   v       HighToLow a
           vB = VectorDeclaration AssignTo   (v + 1) HighToLow b
           vC = VectorDeclaration AssignFrom (v + 2) HighToLow s
       put (NetlistGenerationState (v + 3) (vA:vB:vC:vDecs))
       return ("  assign v" ++ show (v + 2) ++ " = v" ++ show v ++
               " + v" ++ show (v + 1) ++ ";")
computeVectors' (otherInst, instNr) = return (generateInstance otherInst instNr)

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

generateInstance :: Netlist.PrimitiveInstance -> Int -> String
generateInstance inst@(Netlist.BindPrimitive _ _ Netlist.DelayBit iAny oAny) _
  = "  always_ff @(posedge clk) net[" ++ show (fromN o) ++
    "] <= rst ? 1'b0 : net[" ++ show (fromN i) ++ "];"
    where
    i = unsafeCoerce iAny :: BinNums.N
    o = unsafeCoerce oAny :: BinNums.N
generateInstance inst@(Netlist.BindPrimitive _ _ Netlist.AssignBit aAny bAny) _
   = "  assign net[" ++ show (fromN a) ++ "] = net[" ++ show (fromN b) ++ "];"
     where
     a = unsafeCoerce aAny :: BinNums.N
     b = unsafeCoerce bAny :: BinNums.N
generateInstance inst@(Netlist.BindPrimitive _ _ (Netlist.WireInputBit name) _ oAny) _
   = "  assign net[" ++ show (fromN o) ++ "] = " ++ name ++ ";"
     where
     o = unsafeCoerce oAny :: BinNums.N
generateInstance inst@(Netlist.BindPrimitive _ _ (Netlist.WireInputBitVec name s) _ oAny) _
   = unlines
     ["  assign net[" ++ show (fromN n) ++ "] = " ++ name ++ "[" ++ show i ++
     "];" | (n, i) <- zip o [0..s - 1]]
     where
     o = unsafeCoerce oAny :: [BinNums.N]
generateInstance inst@(Netlist.BindPrimitive _ _ (Netlist.WireOutputBit name) oAny o) _ 
   = "  assign " ++ name ++ " = net[" ++ show (fromN o) ++ "] ;"
     where
     o = unsafeCoerce oAny :: BinNums.N
generateInstance inst@(Netlist.BindPrimitive _ _ (Netlist.WireOutputBitVec name s) oAny _) _
   = unlines
     ["  assign " ++ name ++ "[" ++ show i ++ "] = net[" ++ show (fromN n) ++ 
     "];" | (n, i) <- zip o [0.. s - 1]]    
     where
     o = unsafeCoerce oAny :: [BinNums.N]        
generateInstance (Netlist.BindPrimitive _ _ (Netlist.UnsignedAdd _ _ _) ab s) _
   = "" -- Generated instead during vector generation
generateInstance inst@(Netlist.BindPrimitive i o prim _ _) instNr
  = "  " ++ instName ++ " inst" ++ "_" ++ show instNr ++ " " ++
    showArgs args ++ ";"
    where
    instName = maybe (error "Request for un-namable instance") id $ Netlist.primitiveName i o prim
    args = maybe (error "Primitive did not have extractable arguments!") id $ Netlist.instanceArgs inst
  
showArgs :: [BinNums.N] -> String
showArgs args = "(" ++ concat (insertCommas (map showArg args)) ++ ")";

showArg :: BinNums.N -> String
showArg n = "net[" ++ show (fromN n) ++ "]"

--------------------------------------------------------------------------------
-- Generate test bench
--------------------------------------------------------------------------------

generateTestBench :: CircuitInterface -> [String]
generateTestBench (Coq_mkCircuitInterface  name inputShape outputShape attrs)
  = ["// Automatically generated SystemVerilog 2012 code from Cava",
     "// Please do not hand edit.",
     "",
     "module " ++ name ++ "_tb(",
     "  input logic clk",
     ");",
     "",
     "  " ++ name ++ " " ++ name ++ "_inst (.*);",
     ""] ++
     declareLocalPorts inputShape ++
     declareLocalPorts outputShape ++
    ["",
     "endmodule"
    ]

declareLocalPorts :: Coq_shape (String, Coq_portType) -> [String]
declareLocalPorts shape
  = map declareLocalPort portList
    where
    portList :: [PortDeclaration]  = shapeToPortDeclaration shape

declareLocalPort :: PortDeclaration -> String
declareLocalPort (Coq_mkPort name portType) =
  case portType of
    Bit -> "logic " ++ name ++ ";"
    BitVec xs -> "logic " ++ concat ["[" ++ show (i - 1) ++ ":0]" | i <- xs] ++
                 " " ++ name ++ ";"
 