{- Copyright 2021 The Project Oak Authors

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

--------------------------------------------------------------------------------
-- Generate test bench
--------------------------------------------------------------------------------

module TestBench
where

import Netlist
import Signal

import SystemVerilogUtils

writeTestBench :: TestBench -> IO ()
writeTestBench testBench
  = do putStr ("Generating test bench " ++ filename ++ " " ++ driver ++ "...")
       writeFile filename (unlines (generateTestBench testBench))
       writeFile driver (unlines (cppDriver name clk ticks))
       writeFile (name ++ ".tcl") (unlines (tclScript name ticks))
       putStrLn (" [done]")
    where
    name = testBenchName testBench
    filename = name ++ ".sv"
    driver = name ++ ".cpp"
    ticks = length (testBenchInputs testBench)
    clk' = clkName (testBenchInterface testBench)
    clk = if clk' == "" then
            "clk" -- This is a combinational circuit, use make up a clock
                  -- name for the test bench ticks.
          else
            clk'

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
    [] ++
    (if length (testBenchInputs testBench) == 0 then [] else body) ++
    [] ++
    ["endmodule"
    ]
    where
    intf = testBenchInterface testBench
    name = circuitName intf
    inputPortList = circuitInputs intf
    outputPortList = circuitOutputs intf
    nrTests = length (testBenchInputs testBench)
    body =
      ["  // Input test vectors"] ++
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
      "  end"
      ]

declareLocalPorts ::  [PortDeclaration] -> [String]
declareLocalPorts = map declareLocalPort

declareLocalPort :: PortDeclaration -> String
declareLocalPort port
  = declarePort port ++ ";"

declarePort :: PortDeclaration -> String
declarePort (Coq_mkPort name kind) =
  case kind of
    Bit -> "  (* mark_debug = \"true\" *) logic " ++ name
    Vec k s -> "  (* mark_debug = \"true\" *) " ++ vectorDeclaration name k s

initTestVectors :: [PortDeclaration] -> [[SignalExpr]] -> [String]
initTestVectors _ [] = [] -- No test vectors provided, SystemVerilog does not permit zero length arrays
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

-- Construct vector literals assuming downto indexing.
showSignalExpr :: SignalExpr -> String
showSignalExpr (BitVal v)   = "    1'b" ++ showBit v
showSignalExpr (VecVal xs) | isAllBits xs
  = "    " ++ show (length xs) ++ "'d" ++ show (signalToInt xs)
showSignalExpr (VecVal xs)
  = "    '{ " ++ concat (insertCommas (map showSignalExpr (reverse xs))) ++ " }"

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
formatPortWithName (Coq_mkPort name (Vec Bit _)) = " " ++ name ++ " = %0d"
formatPortWithName (Coq_mkPort name (Vec (Vec _ _) s))
  = concat (insertCommas [" " ++ name ++ "[" ++ show i ++ "] = %0d" |
            i  <- [0..s-1]])

smashPorts :: PortDeclaration -> String
smashPorts portDec
  = case port_type portDec of
      Bit -> name
      Vec Bit _ -> name
      Vec (Vec _ _) s ->
        concat (insertCommas [name ++ "[" ++ show i ++ "]" | i <- [0..s-1]])
    where
    name = port_name portDec

checkOutputs :: [PortDeclaration] -> [String]
checkOutputs ports = concat (map checkOutput ports)

checkOutput :: PortDeclaration -> [String]
checkOutput port
  = ["      if(" ++ name ++ " != " ++ name ++ "_vectors[i_cava]) begin",
     "        $error (\"For " ++ name ++ " expected " ++ fmt ++ " but got " ++
     fmt ++ "\", " ++ name ++ "_vectors[i_cava], " ++ name ++ ");",
     "      end;"
    ]
    where
    fmt = formatKind (port_type port)
    name = port_name port

formatKind :: SignalType -> String
formatKind Bit = "%0b"
formatKind (Vec Bit _) = "%0d"
formatKind other = "error: attempt to format unknown kind"

cppDriver :: String -> String -> Int -> [String]
cppDriver name clkName ticks =
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
    "    top->" ++ clkName ++ " = 0; main_time += 5;",
    "    top->eval(); vcd_trace->dump(main_time);",
    "    top->" ++ clkName ++ " = 1;  main_time += 5;",
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