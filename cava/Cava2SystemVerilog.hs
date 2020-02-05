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

{-# LANGUAGE StandaloneDeriving #-}

module Cava2SystemVerilog
where

import qualified Cava

deriving instance Show Cava.PortType
deriving instance Show Cava.PortDeclaration

writeSystemVerilog :: Cava.CavaState -> IO ()
writeSystemVerilog netlist
  = writeFile (Cava.moduleName netlist ++ ".sv")
              (unlines (cava2SystemVerilog netlist))

cava2SystemVerilog :: Cava.CavaState -> [String]
cava2SystemVerilog (Cava.Coq_mkCavaState moduleName netNumber instances
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

inputPorts :: [Cava.PortDeclaration] -> [String]
inputPorts = map inputPort

inputPort :: Cava.PortDeclaration -> String
inputPort (Cava.Coq_mkPort name (Cava.BitPort _)) = "  input logic " ++ name
inputPort (Cava.Coq_mkPort name (Cava.VectorTo0Port v)) 
  = "  input logic[" ++ show ((length v) - 1) ++ ":0] " ++ name
inputPort (Cava.Coq_mkPort name (Cava.VectorFrom0Port v)) 
  = "  input logic[0:" ++ show (length v - 1) ++ "] " ++ name

outputPorts :: [Cava.PortDeclaration] -> [String]
outputPorts = map outputPort

outputPort :: Cava.PortDeclaration -> String
outputPort (Cava.Coq_mkPort name (Cava.BitPort _)) = "  output logic " ++ name
outputPort (Cava.Coq_mkPort name (Cava.VectorTo0Port v)) 
  = "  output logic[" ++ show ((length v) - 1) ++ ":0] " ++ name
outputPort (Cava.Coq_mkPort name (Cava.VectorFrom0Port v)) 
  = "  output logic[0:" ++ show (length v - 1) ++ "] " ++ name

insertCommas :: [String] -> [String]
insertCommas [] = []
insertCommas [x] = [x]
insertCommas (x:y:xs) = (x ++ ",") : insertCommas (y:xs)

nameOfInstance :: Cava.Primitive -> String
nameOfInstance inst
  = case inst of
      Cava.Not _ _ -> "not"
      Cava.And _ _ -> "and"
      Cava.Nand _ _ -> "nand"
      Cava.Or _ _ -> "or"
      Cava.Nor _ _ -> "nor"
      Cava.Xor _ _-> "xor"
      Cava.Xnor _ _ -> "xnor"
      Cava.Buf _ _ -> "buf"
      Cava.Xorcy _ _ _ -> "XORCY"
      Cava.Muxcy _ _ _ _ -> "MUXCY"

instanceArgs :: Cava.Primitive -> [Integer]
instanceArgs inst
  = case inst of
      Cava.Not i o -> [o, i]
      Cava.And i o -> o:i
      Cava.Nand i o -> o:i
      Cava.Or i o -> o:i
      Cava.Nor i o -> o:i
      Cava.Xor i o -> o:i
      Cava.Xnor i o -> o:i
      Cava.Buf i o -> [o, i]
      Cava.Xorcy li ci o -> [o, ci, li]
      Cava.Muxcy s di ci o -> [o, ci, di, s]

generateInstance :: Cava.Instance -> String
generateInstance (Cava.Coq_mkInstance number (Cava.DelayBit i o))
   = "  always_ff @(posedge clk) if (rst) net[" ++ 
        show o ++ "] <= 1'b0; else net[" ++ show o ++ "] <= net[" ++ show i ++
     "];"
generateInstance (Cava.Coq_mkInstance number inst)      
  = "  " ++ instName ++ " inst" ++ show number ++ " " ++  showArgs args ++ ";"
   where
   instName = nameOfInstance inst
   args = instanceArgs inst

showArgs :: [Integer] -> String
showArgs args = "(" ++ concat (insertCommas (map showArg args)) ++ ")";

showArg :: Integer -> String
showArg n = "net[" ++ show n ++ "]"

wireInput :: Cava.PortDeclaration -> [String]
wireInput (Cava.Coq_mkPort name (Cava.BitPort n))
  = ["  assign net[" ++ show n ++ "] = " ++ name ++ ";"]
wireInput (Cava.Coq_mkPort name (Cava.VectorTo0Port v)) 
  = ["  assign net[" ++ show n ++ "] = " ++ name ++ "[" ++ show i ++ "];" |
     (n, i) <- zip v [0..length v - 1]]

wireOutput :: Cava.PortDeclaration -> [String]
wireOutput (Cava.Coq_mkPort name (Cava.BitPort n))
  = ["  assign " ++ name ++ " = net[" ++ show n ++ "] ;"]
wireOutput (Cava.Coq_mkPort name (Cava.VectorTo0Port v)) 
  = ["  assign " ++ name ++ "[" ++ show i ++ "] = net[" ++ show n ++ "];" |
     (n, i) <- zip v [0..length v - 1]]
