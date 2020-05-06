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

import qualified BinNums
import Netlist

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
    ["  );",
     "",
     "  logic[" ++ show (fromN netNumber-1) ++ ":0] net;"] ++
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
inputPort (Netlist.Coq_mkPort name (BitVec sizes))
  = "  input " ++ vectorDeclaration name sizes

vectorDeclaration :: String -> [Integer] -> String
vectorDeclaration name sizes
  = "logic["++ show (base - 1) ++ ":0] " ++ name ++ multi
    where
    base = last sizes
    multi = concat ["[" ++ show i ++ "]" | i <- reverse (init sizes)]

outputPorts :: [Netlist.PortDeclaration] -> [String]
outputPorts = map outputPort

outputPort :: Netlist.PortDeclaration -> String
outputPort (Netlist.Coq_mkPort name Bit) = "  output logic " ++ name
outputPort (Netlist.Coq_mkPort name (BitVec sizes))
  = "  output " ++ vectorDeclaration name sizes

insertCommas :: [String] -> [String]
insertCommas [] = []
insertCommas [x] = [x]
insertCommas (x:y:xs) = (x ++ ",") : insertCommas (y:xs)

data VectorDirection = HighToLow | LowToHigh
                       deriving (Eq, Show)

data VectorAssignment = AssignTo | AssignFrom

data VectorDeclaration
  = VectorDeclaration VectorAssignment Int [BinNums.N]

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
       let vA = VectorDeclaration AssignTo   v       a
           vB = VectorDeclaration AssignTo   (v + 1) b
           vC = VectorDeclaration AssignFrom (v + 2) s
       put (NetlistGenerationState (v + 3) (vA:vB:vC:vDecs))
       return ("  assign v" ++ show (v + 2) ++ " = v" ++ show v ++
               " + v" ++ show (v + 1) ++ ";")
computeVectors' (otherInst, instNr) = return (generateInstance otherInst instNr)

declareVectors :: [VectorDeclaration] -> [String]
declareVectors = map declareVector

declareVector :: VectorDeclaration -> String
declareVector (VectorDeclaration _ i bvec)
  = "  logic[" ++ range ++ "] v" ++ show i ++ ";"
    where
    s = length bvec
    range = show (s - 1) ++ ":0"

populateVectors :: [VectorDeclaration] -> [String]
populateVectors = concat . map populateVector

populateVector :: VectorDeclaration -> [String]
populateVector (VectorDeclaration AssignTo v nets)
  = if sequentialUp nets' then
      ["  assign v" ++ show v ++ " = net[" ++
         show (last nets') ++ ":" ++ show (head nets') ++ "];"]
    else
      ["  assign v" ++ show v ++ "[" ++ show i ++
       "] = net[" ++ show li ++ "];" | (i, li) <- zip [0..] nets']
    where
    nets' = map fromN nets
populateVector (VectorDeclaration AssignFrom v nets)
  = if sequentialUp nets' then
      ["  assign net[" ++ show (last nets') ++ ":" ++ show (head nets') ++
        "] = v" ++ show v ++ ";"]
    else
      ["  assign net[" ++ show li ++ "] = v" ++ show v ++
       "[" ++ show i ++ "];" | (i, li) <- zip [0..] nets']
    where
    nets' = map fromN nets

sequentialUp :: [Integer] -> Bool
sequentialUp [x] = True
sequentialUp (x:y:z)
  = if y == x + 1 then
      sequentialUp (y:z)
    else
       False

--------------------------------------------------------------------------------
-- Mappings to/from multi-dimensional bit-vectors.
--------------------------------------------------------------------------------

assignMultiDimensionalInput :: String -> String -> [Integer] ->
                               Coq_signalTy BinNums.N -> [String]
assignMultiDimensionalInput _ _ [] _ = []
assignMultiDimensionalInput name prefix [s] oAny
  = if sequentialUp oN then
      ["  assign net" ++ "[" ++ show (last oN) ++ ":" ++ show (head oN) ++
       "] = " ++ name ++ prefix ++ ";"]
    else
      ["  assign net" ++ "[" ++ show n ++ "] = " ++ name ++ prefix ++ "[" ++ show i ++
       "];" | (n, i) <- zip oN [0..s - 1]]
     where
     o = unsafeCoerce oAny :: [BinNums.N]
     oN = map fromN o
assignMultiDimensionalInput name prefix (x:xs) oAny
  = concat [assignMultiDimensionalInput name (prefix ++ "[" ++ show p ++ "]") xs o
           | (p, o) <- zip [0..x-1] os]
     where
     os = unsafeCoerce oAny :: [Coq_signalTy BinNums.N]

assignMultiDimensionalOutput :: String -> String -> [Integer] ->
                                Coq_signalTy BinNums.N -> [String]
assignMultiDimensionalOutput _ _ [] _ = []
assignMultiDimensionalOutput name prefix [s] oAny
  = if sequentialUp oN then
      ["  assign " ++ name ++ " = net[" ++ show (last oN) ++ ":" ++ show (head oN) ++ "];"]
    else
      ["  assign " ++ name ++ "[" ++ show i ++ "] = net[" ++ show n ++ 
       "];" | (n, i) <- zip oN [0.. s - 1]]  
     where
     o = unsafeCoerce oAny :: [BinNums.N]
     oN = map fromN o
assignMultiDimensionalOutput name prefix (x:xs) oAny
  = concat [assignMultiDimensionalOutput name (prefix ++ "[" ++ show p ++ "]") xs o
           | (p, o) <- zip [0..x-1] os]
     where
     os = unsafeCoerce oAny :: [Coq_signalTy BinNums.N]

--------------------------------------------------------------------------------
-- Generate SystemVerilog for a specific instance.
--------------------------------------------------------------------------------

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
generateInstance inst@(Netlist.BindPrimitive _ _
                   (Netlist.WireInputBitVec name sizes) _ oAny) _
   = unlines (assignMultiDimensionalInput name "" sizes oAny)
generateInstance inst@(Netlist.BindPrimitive _ _ (Netlist.WireOutputBit name) oAny o) _ 
   = "  assign " ++ name ++ " = net[" ++ show (fromN o) ++ "] ;"
     where
     o = unsafeCoerce oAny :: BinNums.N
generateInstance inst@(Netlist.BindPrimitive _ _
                 (Netlist.WireOutputBitVec name sizes) oAny _) _
   = unlines (assignMultiDimensionalOutput name "" sizes oAny)   
generateInstance inst@(Netlist.BindPrimitive _ _
                 (Netlist.Lut1 config) iAny oAny) instNr
   = "  LUT1 #(.INIT(2'h" ++
     showHex (fromN config) "" ++ ")) lut1_" ++ show instNr ++ " "
     ++ showArgs [o, i] ++ ";"
     where
     i = unsafeCoerce iAny :: BinNums.N
     o = unsafeCoerce oAny :: BinNums.N
generateInstance inst@(Netlist.BindPrimitive _ _
                 (Netlist.Lut2 config) i0i1Any oAny) instNr
   = "  LUT2 #(.INIT(4'h" ++
     showHex (fromN config) "" ++ ")) lut2_" ++ show instNr ++ " "
     ++ showArgs args ++ ";"
     where
     args = maybe (error "Primitive did not have extractable arguments!") id $ Netlist.instanceArgs inst
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

writeTestBench :: TestBench -> IO ()
writeTestBench testBench
  = do putStr ("Generating test bench " ++ filename ++ " " ++ driver ++ "...")
       writeFile filename (unlines (generateTestBench testBench))
       writeFile driver (unlines (cppDriver name ticks))
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
    inputPortList = shapeToPortDeclaration (circuitInputs intf)
    outputPortList = shapeToPortDeclaration (circuitOutputs intf)
    nrTests = length (testBenchInputs testBench)

declareCircuitPorts :: Coq_shape (String, Coq_portType) -> [String]
declareCircuitPorts shape
  = insertCommas (map declareCircuitPort portList)
    where
    portList :: [PortDeclaration]  = shapeToPortDeclaration shape

declareCircuitPort :: PortDeclaration -> String
declareCircuitPort port
  = "  output " ++ declarePort port

declareLocalPorts :: Coq_shape (String, Coq_portType) -> [String]
declareLocalPorts shape
  = map declareLocalPort portList
    where
    portList :: [PortDeclaration]  = shapeToPortDeclaration shape

declareLocalPort :: PortDeclaration -> String
declareLocalPort port
  = declarePort port ++ ";"

declarePort :: PortDeclaration -> String
declarePort (Coq_mkPort name portType) =
  case portType of
    Bit -> "  (* mark_debug = \"true\" *) logic " ++ name 
    BitVec xs -> "  (* mark_debug = \"true\" *) " ++ vectorDeclaration name xs 

initTestVectors :: [PortDeclaration] -> [[Signal]] -> [String]
initTestVectors [] _ = []
initTestVectors (p:ps) s
  = initTestVector p (map head s) ++
    initTestVectors ps (map tail s)
  
initTestVector :: PortDeclaration -> [Signal] -> [String]
initTestVector pd@(Coq_mkPort name typ) s
  = [declarePort (Coq_mkPort name' typ) ++ " = '{"] ++
    insertCommas (map showSignal s) ++
    ["    };"]
    where
    name' = name ++ "_vectors[" ++ show (length s) ++ "]"

showSignal :: Signal -> String
showSignal (BitVal v)   = "    1'b" ++ showBit v
showSignal (VecVal xs) | isAllBits xs
  = "    " ++ show (length xs) ++ "'d" ++ show (signalToInt xs)
showSignal (VecVal xs)
  = "    '{ " ++ concat (insertCommas (map showSignal xs )) ++ " }"  
     
isAllBits :: [Signal] -> Bool
isAllBits = and . map isBitVal

isBitVal :: Signal -> Bool
isBitVal (BitVal _) = True
isBitVal _ = False

signalToInt :: [Signal] -> Integer
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
formatPortWithName (Coq_mkPort name (BitVec [x])) = " " ++ name ++ " = %0d"
formatPortWithName (Coq_mkPort name (BitVec xs))
  = concat (insertCommas [" " ++ name ++ i ++ " = %0d" | i  <- formIndices (init xs)])

formIndices ::  [Integer] -> [String]
formIndices [] = []
formIndices (x:xs)
  = ["[" ++ show i ++ "]" ++ concat (formIndices xs) | i <- [0..x-1]]

smashPorts :: PortDeclaration -> String
smashPorts portDec
  = case port_shape portDec of
      Bit -> name
      BitVec [x] -> name
      BitVec xs -> concat (insertCommas [name ++ i | i <- formIndices (init xs)])
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
    fmt = formatPortType (port_shape port)
    name = port_name port

formatPortType :: Coq_portType -> String
formatPortType Bit = "%0b"
formatPortType (BitVec _) = "%0d"

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
