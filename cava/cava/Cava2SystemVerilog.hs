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
import Numeric
import qualified Vector

import qualified BinNums
import Netlist
import Kind
import Signal
import Types

writeSystemVerilog :: CavaState -> IO ()
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
cava2SystemVerilog (Netlist.Coq_mkCavaState netNumber vCount vDefs
                    clk clkEdge rst rstEdge
                    (Netlist.Coq_mkModule moduleName instances
                    inputs outputs))
  = ["module " ++ moduleName ++ "("] ++

    insertCommas (inputPorts inputs ++ outputPorts outputs) ++
    ["  );"] ++
    ["",
     "  timeunit 1ns; timeprecision 1ns;",
     "",
     "  logic zero;",
     "  logic one;"] ++
    declareLocalNets (fromN netNumber) ++
    [vectorDeclaration ("v" ++ show i) k s ++ ";" | ((k, s), i) <- zip vDefs [0..]] ++
    [""] ++
    ["  // Constant nets",
     "  assign zero = 1'b0;",
     "  assign one = 1'b1;"] ++
    [""] ++
    [generateInstance genState inst i | (inst, i) <- zip instances [0..]] ++
    [""] ++
    ["endmodule"]
    where
    genState = NetlistGenerationState clk clkEdge rst rstEdge

declareLocalNets :: Integer -> [String]
declareLocalNets n
  = if n == 0 then
      []
    else
      ["  logic[" ++ show (n-1) ++ ":0] net;"]

data NetlistGenerationState
  = NetlistGenerationState (Maybe Signal) SignalEdge (Maybe Signal) SignalEdge

inputPorts :: [Netlist.PortDeclaration] -> [String]
inputPorts = map inputPort

inputPort :: Netlist.PortDeclaration -> String
inputPort (Netlist.Coq_mkPort name Bit) = "  input logic " ++ name
inputPort (Netlist.Coq_mkPort name (BitVec k s))
  = "  input " ++ vectorDeclaration name k s

vectorDeclaration :: String -> Kind -> Integer -> String
vectorDeclaration name k s
  = case k of
      Bit -> "  logic[" ++ show (s - 1) ++ ":0] " ++ name
      BitVec k2 s2 -> vectorDeclaration name k2 s2 ++ "[" ++ show s ++ "]"

outputPorts :: [Netlist.PortDeclaration] -> [String]
outputPorts = map outputPort

outputPort :: Netlist.PortDeclaration -> String
outputPort (Netlist.Coq_mkPort name Bit) = "  output logic " ++ name
outputPort (Netlist.Coq_mkPort name (BitVec k s))
  = "  output " ++ vectorDeclaration name k s

insertCommas :: [String] -> [String]
insertCommas [] = []
insertCommas [x] = [x]
insertCommas (x:y:xs) = (x ++ ",") : insertCommas (y:xs)

showVectorElements :: [Signal] -> String
showVectorElements e
  = concat (insertCommas (map showSignal e))

showVecLiteral :: Kind -> [Signal] -> String
showVecLiteral k e
  = case k of 
      Bit -> -- Packed vector, downto indexing
             "{" ++ showVectorElements (reverse e) ++ "}"
      _   -> -- unpacked vector, upto indexing
             "'{" ++ showVectorElements e ++ "}"

showSignal :: Signal -> String
showSignal signal
  = case signal of
      UndefinedSignal -> error "Attempt to use an undefined signal"
      UninterpretedSignal _ name -> name
      Gnd -> "zero"
      Vcc -> "one"
      Wire n -> "net[" ++ show (fromN n) ++ "]"
      NamedWire name -> name
      NamedVector _ _ name -> name
      LocalBitVec _ _ v -> "v" ++ show (fromN v)
      VecLit k s vs -> showVecLiteral k (Vector.to_list s vs)
      IndexAt _ _ _ v i -> showSignal v ++ "[" ++ showSignal i ++ "]"
      IndexConst _ _ v i -> showSignal v ++ "[" ++ show i ++ "]"
      Slice _ _ start len v -> showSignal v ++ "[" ++ show (start + len - 1) ++
                               ":" ++ show start ++ "]"

--------------------------------------------------------------------------------
-- Generate SystemVerilog for a specific instance.
--------------------------------------------------------------------------------

generateInstance :: NetlistGenerationState -> Instance -> Int -> String
generateInstance netlistState (DelayBit i o) _
  = unlines [
    "  always_ff @(" ++ showEdge clkEdge ++ " " ++ showSignal clk ++ " or "
                     ++ showEdge rstEdge ++ " " ++ showSignal rst ++ ") begin",
    "    if (" ++ negReset ++ showSignal rst ++ ") begin",
    "      " ++ showSignal o ++ " <= 1'b0;",
    "    end else begin",
    "      " ++ showSignal o ++ " <= " ++ showSignal i ++ ";",
         "end",
    "  end"]
    where
    NetlistGenerationState (Just clk) clkEdge (Just rst) rstEdge = netlistState
    showEdge edge = case edge of
                      PositiveEdge -> "posedge"
                      NegativeEdge -> "negedge"
    negReset = case rstEdge of
                 PositiveEdge -> ""
                 NegativeEdge -> "!"
generateInstance _ (AssignSignal _ a b) _
   = "  assign " ++ showSignal a ++ " = " ++ showSignal b ++ ";"
generateInstance _ (Not i o) instrNr = primitiveInstance "not" [o, i] instrNr
generateInstance _ (And i0 i1 o) instrNr = primitiveInstance "and" [o, i0, i1] instrNr
generateInstance _ (Nand i0 i1 o) instrNr = primitiveInstance "nand" [o, i0, i1] instrNr
generateInstance _ (Or i0 i1 o) instrNr = primitiveInstance "or" [o, i0, i1] instrNr
generateInstance _ (Nor i0 i1 o) instrNr = primitiveInstance "nor" [o, i0, i1] instrNr
generateInstance _ (Xor i0 i1 o) instrNr = primitiveInstance "xor" [o, i0, i1] instrNr
generateInstance _ (Xnor i0 i1 o) instrNr = primitiveInstance "xnor" [o, i0, i1] instrNr
generateInstance _ (Buf i o) instrNr = primitiveInstance "buf" [o, i] instrNr
generateInstance _ (Component _ name parameters connections) instNr =
  mkInstance name parameters connections instNr
generateInstance _ (UnsignedAdd _ _ _ a b c) _
   = "  assign " ++ showSignal c ++ " = " ++ showSignal a ++ " + " ++ showSignal b ++ ";"

primitiveInstance :: String -> [Signal] -> Int -> String
primitiveInstance instName args instNr
  = "  " ++ instName ++ " inst" ++ "_" ++ show instNr ++ " " ++
    showArgs args ++ ";"
  
showArgs :: [Signal] -> String
showArgs args = "(" ++ concat (insertCommas (map showSignal args)) ++ ")";

mkInstance :: String -> [(String, ConstExpr)] -> [(String, Signal)] ->
              Int -> String
mkInstance instName [] args instNr
  = "  " ++ instName ++ " inst" ++ "_" ++ show instNr ++ " " ++
    showPortArgs args ++ ";"              
mkInstance instName parameters args instNr
  = "  " ++ instName ++ showParameters parameters ++ " inst" ++ "_" ++
    show instNr ++ " " ++
    showPortArgs args ++ ";"

showPortArgs :: [(String, Signal)] -> String
showPortArgs args = "(" ++ concat (insertCommas (map showPortArg args)) ++ ")";

showPortArg :: (String, Signal) -> String
showPortArg (p, n) = "." ++ p ++ "(" ++ showSignal n ++ ")"

showParameters :: [(String, ConstExpr)] -> String
showParameters parameters
  = " #(" ++ concat (insertCommas (map showParameter parameters)) ++ ")";

showParameter :: (String, ConstExpr) -> String
showParameter (name, constExpr)
  = "." ++ name ++ "(" ++ showConstExpr constExpr ++ ")"

showConstExpr :: ConstExpr -> String
showConstExpr constExpr =
  case constExpr of
    HexLiteral w v -> show w ++ "'h" ++ showHex (fromN v) ""
    StringLiteral s -> "\"" ++ s ++ "\""

--------------------------------------------------------------------------------
-- Generate test bench
--------------------------------------------------------------------------------

writeTestBench :: TestBench -> IO ()
writeTestBench testBench
  = do putStr ("Generating test bench " ++ filename ++ " " ++ driver ++ "...")
       writeFile filename (unlines (generateTestBench testBench))
       writeFile driver (unlines (cppDriver name ticks))
       writeFile (name ++ ".tcl") (unlines (tclScript name ticks))
       putStrLn (" [done]")
    where
    name = testBenchName testBench
    filename = name ++ ".sv"
    driver = name ++ ".cpp"
    ticks = length (testBenchInputs testBench) 

generateTestBench :: TestBench -> [String]
generateTestBench testBench
  = ["// Automatically generated SystemVerilog 2012 code from Cava",
     "// Please do not hand edit.",
     "",
     "module " ++ (testBenchName testBench) ++ "(",
     "  input logic clk",
     ");",
     "",
     "  timeunit 1ns; timeprecision 1ns;",
     "",
     "  logic rst;",
     "",
     "  " ++ name ++ " " ++ name ++ "_inst (.*);",
     "",
     "  // Circuit inputs"] ++
     declareLocalPorts (circuitInputs intf) ++
    ["  // Circuit outputs"] ++
     declareLocalPorts (circuitOutputs intf) ++
     ["",
      "  // Input test vectors"] ++
     initTestVectors inputPortList (testBenchInputs testBench) ++
     ["",
      "  // Expected output test vectors"] ++
     initTestVectors outputPortList (testBenchExpectedOutputs testBench) ++
    ["",
     "  int unsigned i_cava = 0;"] ++
     assignInputs inputPortList ++
    ["",
     "  always @(posedge clk) begin"
     ] ++
     [addDisplay (inputPortList ++ outputPortList)] ++
     checkOutputs outputPortList ++
    ["    if (i_cava == " ++ show (nrTests - 1) ++ ") begin",
     "      $display (\"PASSED\");",
     "      i_cava <= 0;",
     "    end else begin",
     "      i_cava <= i_cava + 1 ;",
     "    end;",
     "  end",
     "",
     "endmodule"
    ]
    where
    intf = testBenchInterface testBench
    name = circuitName intf
    inputPortList = flattenShape (circuitInputs intf)
    outputPortList = flattenShape (circuitOutputs intf)
    nrTests = length (testBenchInputs testBench)

declareCircuitPorts :: Coq_shape PortDeclaration -> [String]
declareCircuitPorts shape
  = insertCommas (map declareCircuitPort portList)
    where
    portList :: [PortDeclaration]  = flattenShape shape

declareCircuitPort :: PortDeclaration -> String
declareCircuitPort port
  = "  output " ++ declarePort port

declareLocalPorts :: Coq_shape PortDeclaration -> [String]
declareLocalPorts shape
  = map declareLocalPort portList
    where
    portList :: [PortDeclaration] = flattenShape shape

declareLocalPort :: PortDeclaration -> String
declareLocalPort port
  = declarePort port ++ ";"

declarePort :: PortDeclaration -> String
declarePort (Coq_mkPort name kind) =
  case kind of
    Bit -> "  (* mark_debug = \"true\" *) logic " ++ name 
    BitVec k s -> "  (* mark_debug = \"true\" *) " ++ vectorDeclaration name k s 

initTestVectors :: [PortDeclaration] -> [[SignalExpr]] -> [String]
initTestVectors [] _ = []
initTestVectors (p:ps) s
  = initTestVector p (map head s) ++
    initTestVectors ps (map tail s)
  
initTestVector :: PortDeclaration -> [SignalExpr] -> [String]
initTestVector pd@(Coq_mkPort name typ) s
  = [declarePort (Coq_mkPort name' typ) ++ " = '{"] ++
    insertCommas (map showSignalExpr s) ++
    ["    };"]
    where
    name' = name ++ "_vectors[" ++ show (length s) ++ "]"

showSignalExpr :: SignalExpr -> String
showSignalExpr (BitVal v)   = "    1'b" ++ showBit v
showSignalExpr (VecVal xs) | isAllBits xs
  = "    " ++ show (length xs) ++ "'d" ++ show (signalToInt xs)
showSignalExpr (VecVal xs)
  = "    '{ " ++ concat (insertCommas (map showSignalExpr xs )) ++ " }"  
     
isAllBits :: [SignalExpr] -> Bool
isAllBits = and . map isBitVal

isBitVal :: SignalExpr -> Bool
isBitVal (BitVal _) = True
isBitVal _ = False

signalToInt :: [SignalExpr] -> Integer
signalToInt [] = 0
signalToInt ((BitVal b):xs)
  = case b of
      False -> 2 * signalToInt xs
      True -> 1 + 2 * signalToInt xs
signalToBit _ = error "Not a bit-vector"      

showBit :: Bool -> String
showBit False = "0"
showBit True = "1"

assignInputs :: [PortDeclaration] -> [String]
assignInputs = map assignInput

assignInput :: PortDeclaration -> String
assignInput port
  = "  assign " ++ port_name port ++ " = " ++ port_name port ++ "_vectors[i_cava];"

addDisplay ::  [PortDeclaration] -> String
addDisplay ports
  = "      $display(\"" ++ formatArgs ++ "\", $time, " ++ formatPars ++ ");"
    where
    formatArgs = concat (insertCommas
                         ("%t: tick = %0d": map formatPortWithName ports))
    formatPars = concat (insertCommas ("i_cava": map smashPorts ports))

formatPortWithName :: PortDeclaration -> String
formatPortWithName (Coq_mkPort name Bit) = " " ++ name ++ " = %0b"
formatPortWithName (Coq_mkPort name (BitVec Bit _)) = " " ++ name ++ " = %0d"
formatPortWithName (Coq_mkPort name (BitVec (BitVec _ _) s))
  = concat (insertCommas [" " ++ name ++ "[" ++ show i ++ "] = %0d" |
            i  <- [0..s-1]])

smashPorts :: PortDeclaration -> String
smashPorts portDec
  = case port_shape portDec of
      Bit -> name
      BitVec Bit _ -> name
      BitVec (BitVec _ _) s ->
        concat (insertCommas [name ++ "[" ++ show i ++ "]" | i <- [0..s-1]])
    where
    name = port_name portDec

checkOutputs :: [PortDeclaration] -> [String]
checkOutputs ports = concat (map checkOutput ports)

checkOutput :: PortDeclaration -> [String]
checkOutput port
  = ["      if(" ++ name ++ " != " ++ name ++ "_vectors[i_cava]) begin",
     "        $fatal (\"For " ++ name ++ " expected " ++ fmt ++ " but got " ++
     fmt ++ "\", " ++ name ++ "_vectors[i_cava], " ++ name ++ ");",
     "      end;"
    ]
    where
    fmt = formatKind (port_shape port)
    name = port_name port

formatKind :: Kind -> String
formatKind Bit = "%0b"
formatKind (BitVec Bit _) = "%0d"
formatKind other = "error: attempt to format unknown kind"

cppDriver :: String -> Int -> [String]
cppDriver name ticks =
  ["#include <stdlib.h>",
    "#include \"V" ++ name ++ ".h\"",
    "#include \"verilated.h\"",
    "#include \"verilated_vpi.h\"",
    "#include \"verilated_vcd_c.h\"",
    "",
    "double main_time = 0;",
    "double sc_time_stamp() { return main_time; }",
    "",
    "int main(int argc, char **argv) {",
    "  Verilated::commandArgs(argc, argv);",
    "  V" ++ name ++ " *top = new V" ++ name ++ ";",
    "  VerilatedVcdC* vcd_trace = new VerilatedVcdC;",
    "  Verilated::traceEverOn(true);",
    "  top->trace(vcd_trace, 99);",
    "  top->eval(); vcd_trace->dump(main_time);",
    "  vcd_trace->open(\"" ++ name ++ ".vcd\");",
    "  for (unsigned int i = 0; i < " ++ show ticks ++ "; i++) {",
    "    top->clk = 0; main_time += 5;",
    "    top->eval(); vcd_trace->dump(main_time);",
    "    top->clk = 1;  main_time += 5;",
    "    top->eval(); vcd_trace->dump(main_time);",
    "  }",
    "  vcd_trace->close();",
    "  delete top;",
    "  exit(EXIT_SUCCESS);",
    "}"
  ]

-- This function generates a TCL script for driving the top-level
-- testbench generated from Cava for use with the Vivado xsim
-- simulator. The test is run for number of cycles that correspond to
-- the required number of ticks and a VCD wavefile file is generated.
tclScript :: String -> Int -> [String]
tclScript name ticks
  = ["open_vcd " ++ name ++ ".vcd",
     "log_vcd *",
     "log_vcd [ get_objects * ]",
     "add_force {/" ++ name ++ "/clk} {0 0ns} {1 50ns} -repeat_every 100ns",
     "run " ++ show ticks ++ "00ns",
     "flush_vcd",
     "close_vcd",
     "exit"
    ]
