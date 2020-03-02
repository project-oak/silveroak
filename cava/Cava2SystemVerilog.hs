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

import qualified Netlist

writeSystemVerilog :: Netlist.CavaState -> IO ()
writeSystemVerilog netlist
  = writeFile (Netlist.moduleName netlist ++ ".sv")
              (unlines (cava2SystemVerilog netlist))

cava2SystemVerilog :: Netlist.CavaState -> [String]
cava2SystemVerilog (Netlist.Coq_mkCavaState moduleName netNumber instances
                    inputs outputs isSeq)
  = ["module " ++ moduleName ++ "("] ++
    
    insertCommas (clockPorts ++ inputPorts inputs ++ outputPorts outputs) ++
    ["  );"] ++
    ["",
     "  timeunit 1ns; timeprecision 1ns;",
     ""] ++
    ["  logic[" ++ show (netNumber-1) ++ ":0] net;"] ++
    [""] ++
    ["  // Constant nets",
     "  assign net[0] = 1'b0;",
     "  assign net[1] = 1'b1;",
     "  // Wire up inputs."] ++
    concat (map wireInput inputs) ++
    ["  // Wire up outputs."] ++
    concat (map wireOutput outputs) ++
    [""] ++
    map generateInstance instances ++
    [""] ++
    ["endmodule"]
    where
    clockPorts = if isSeq then
                   ["  input logic clk",
                    "  input logic rst"]
                 else
                   []

inputPorts :: [Netlist.PortDeclaration] -> [String]
inputPorts = map inputPort

inputPort :: Netlist.PortDeclaration -> String
inputPort (Netlist.Coq_mkPort name (Netlist.BitPort _)) = "  input logic " ++ name
inputPort (Netlist.Coq_mkPort name (Netlist.VectorTo0Port v)) 
  = "  input logic[" ++ show ((length v) - 1) ++ ":0] " ++ name
inputPort (Netlist.Coq_mkPort name (Netlist.VectorFrom0Port v)) 
  = "  input logic[0:" ++ show (length v - 1) ++ "] " ++ name

outputPorts :: [Netlist.PortDeclaration] -> [String]
outputPorts = map outputPort

outputPort :: Netlist.PortDeclaration -> String
outputPort (Netlist.Coq_mkPort name (Netlist.BitPort _)) = "  output logic " ++ name
outputPort (Netlist.Coq_mkPort name (Netlist.VectorTo0Port v)) 
  = "  output logic[" ++ show ((length v) - 1) ++ ":0] " ++ name
outputPort (Netlist.Coq_mkPort name (Netlist.VectorFrom0Port v)) 
  = "  output logic[0:" ++ show (length v - 1) ++ "] " ++ name

insertCommas :: [String] -> [String]
insertCommas [] = []
insertCommas [x] = [x]
insertCommas (x:y:xs) = (x ++ ",") : insertCommas (y:xs)

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

instanceArgs :: Netlist.Primitive -> [Integer]
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

generateInstance :: Netlist.Instance -> String
generateInstance (Netlist.Coq_mkInstance number (Netlist.DelayBit i o))
   = "  always_ff @(posedge clk) net[" ++ show o ++ "] <= rst ? 1'b0 : net["
        ++ show i ++ "];";
generateInstance (Netlist.Coq_mkInstance number (Netlist.AssignBit a b))
   = "  assign net[" ++ show a ++ "] = net[" ++ show b ++ "];"
generateInstance (Netlist.Coq_mkInstance number inst)      
  = "  " ++ instName ++ " inst" ++ show number ++ " " ++  showArgs args ++ ";"
   where
   instName = nameOfInstance inst
   args = instanceArgs inst

showArgs :: [Integer] -> String
showArgs args = "(" ++ concat (insertCommas (map showArg args)) ++ ")";

showArg :: Integer -> String
showArg n = "net[" ++ show n ++ "]"

wireInput :: Netlist.PortDeclaration -> [String]
wireInput (Netlist.Coq_mkPort name (Netlist.BitPort n))
  = ["  assign net[" ++ show n ++ "] = " ++ name ++ ";"]
wireInput (Netlist.Coq_mkPort name (Netlist.VectorTo0Port v)) 
  = ["  assign net[" ++ show n ++ "] = " ++ name ++ "[" ++ show i ++ "];" |
     (n, i) <- zip v [0..length v - 1]]

wireOutput :: Netlist.PortDeclaration -> [String]
wireOutput (Netlist.Coq_mkPort name (Netlist.BitPort n))
  = ["  assign " ++ name ++ " = net[" ++ show n ++ "] ;"]
wireOutput (Netlist.Coq_mkPort name (Netlist.VectorTo0Port v)) 
  = ["  assign " ++ name ++ "[" ++ show i ++ "] = net[" ++ show n ++ "];" |
     (n, i) <- zip v [0..length v - 1]]
