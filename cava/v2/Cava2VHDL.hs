{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Cava2VHDL where

import Control.Monad.State

import qualified Datatypes

import Cava
import ExtractionUtils

--------------------------------------------------------------------------------
-- writeVHDL generates a VHDL component with the specified name by elaborating
-- the Cava expression expr and writes out generated VHDL to a file with the
-- same name and a ".vhd" suffix.
--------------------------------------------------------------------------------

writeVHDL :: String -> Coq_cava -> IO ()
writeVHDL name expr
  = writeFile (name ++ ".vhd") (unlines (genVHDL name expr))

--------------------------------------------------------------------------------
-- genVHDL will generate a package declaraiton for a component and an
-- entity defining a component for the given Cava expression.
--------------------------------------------------------------------------------

genVHDL :: String -> Coq_cava -> [String]
genVHDL name expr
  =  vhdlPackage isSeqCir name circuitInputs circuitOutputs ++ [""] ++
     vhdlEntity isSeqCir name circuitInputs circuitOutputs ++ [""] ++
     vhdlArchitecture isSeqCir name (netIndex netState) (vhdlCode netState)
     where
     netState :: NetlistState
     (_, netState) = runState (vhdlInstantiation expr undefined) (initState False)
     circuitInputs = map fst (inputs netState)
     circuitOutputs = map fst (outputs netState)
     isSeqCir = isSequential netState

--------------------------------------------------------------------------------
-- The types NetListState and NetExpr are used to elaborate the Cava
-- description. They provide a representation for the names given to the
-- wires that are generated to compose components as well as a monad type
-- representing state operations to gather information about the circuit
-- graph and its inputs and outputs.
--------------------------------------------------------------------------------

data NetlistState
  = NetlistState {netIndex :: Integer,
                  inputs, outputs :: [(String, Integer)],
                  vhdlCode :: [String],
                  isSequential :: Bool}
    deriving (Eq, Show)

-- Move NetExpr to the Coq side, then define Rewire constructor
-- for Cava:
--    | Rewire (NetExpr -> NetExpr)
-- to express arbitrary rewirings.

clk :: Coq_intSignal
clk = unsafeCoerce 2

rst :: Coq_intSignal
rst = unsafeCoerce 3

initState :: Bool -> NetlistState
initState isSeq
  = NetlistState (if isSeq then 4 else 2) [] [] [] isSeq

--------------------------------------------------------------------------------
-- vhdlInstantiation walks the Cava circuit expression and elaborates it.
--------------------------------------------------------------------------------

vhdlInstantiation :: Coq_cava -> Coq_intSignal -> State NetlistState Coq_intSignal
vhdlInstantiation (Input _ name) _
  = do netState <- get
       let o = netIndex netState
           vhdl = vhdlCode netState
           inps = inputs netState
           name' = decodeCoqString name
           assignInput = "  net(" ++ show o ++ ") <= " ++ name' ++ ";"
       put (netState{netIndex = o+1,
                     inputs=(name', o):inps,
                     vhdlCode = assignInput:vhdl})
       return (unsafeCoerce o)
vhdlInstantiation (Unaryop Inv) i = vhdlUnaryOp "inv" i
vhdlInstantiation (Binop And2) i0i1 = vhdlBinaryOp "and2" i0i1
vhdlInstantiation (Binop Xor2) i0i1 = vhdlBinaryOp "xor2" i0i1
vhdlInstantiation (Binop Xorcy) cili
  = case unsafeCoerce cili of
      Datatypes.Coq_pair ci li -> 
        vhdlOpWithPortNames "xorcy" [ci, li] ["ci", "li", "o"]
vhdlInstantiation Muxcy scidi
  = case unsafeCoerce scidi of
      Datatypes.Coq_pair s (Datatypes.Coq_pair ci di) ->
        vhdlOpWithPortNames "muxcy" [s, di, ci] ["s", "di", "ci", "o"]
vhdlInstantiation (Delay _) i
  = do o <- vhdlOpWithPortNames "fdr" [i, clk, rst] ["d", "c", "r", "q"]
       netState <- get
       put (netState{isSequential = True})
       return o
vhdlInstantiation (Compose _ _ _ f g) i
  = do x <- vhdlInstantiation f i
       vhdlInstantiation g x
vhdlInstantiation (Par2 _ _ p q f g) ab
  = do ax <- vhdlInstantiation f a
       bx <- vhdlInstantiation g b
       return (unsafeCoerce (Datatypes.Coq_pair ax bx))
    where
    Datatypes.Coq_pair a b = unsafeCoerce ab        
vhdlInstantiation (Output _ name) o      
  = do netState <- get
       let outs = outputs netState
           vhdl = vhdlCode netState
           name' = decodeCoqString name
           ov :: Integer = unsafeCoerce o
           assignOutput = "  " ++ name' ++ " <= net(" ++ show ov ++ ");"
       put (netState{outputs=(name', ov):outs,
                     vhdlCode=assignOutput:vhdl})
       return (unsafeCoerce o)
vhdlInstantiation (Reshape _ _ f) i = return (f () i)

--------------------------------------------------------------------------------
-- showNet displays a net in VHDL syntax.
--------------------------------------------------------------------------------

vhdlOpWithPortNames :: String -> [Coq_intSignal] -> [String] ->
                       State NetlistState Coq_intSignal
vhdlOpWithPortNames name instantiatedInputs portNames
  = do netState <- get
       let o = netIndex netState
           vhdl = vhdlCode netState
           ii :: [Integer] = map unsafeCoerce instantiatedInputs
           inputPorts = zipWith wireUpPort (init portNames) ii
           allPorts = inputPorts ++ [wireUpPort (last portNames) o]
           inst = "  " ++ name ++ "_" ++ show o ++
                  " : " ++ name ++ " port map (\n" ++
                  unlines (insertCommas allPorts) ++ "  );"
       put (netState{netIndex = o+1, vhdlCode = inst:vhdl})
       return (unsafeCoerce o)
    where
    wireUpPort n i = "    " ++ n ++ " => net(" ++ show i ++ ")"

vhdlUnaryOp :: String -> Coq_intSignal -> State NetlistState Coq_intSignal
vhdlUnaryOp name i =
  vhdlOpWithPortNames name [unsafeCoerce i] ["i", "o"]

vhdlBinaryOp :: String -> Coq_intSignal ->
                State NetlistState Coq_intSignal
vhdlBinaryOp name i0i1
  = case unsafeCoerce i0i1 of
      Datatypes.Coq_pair i0 i1 -> vhdlOpWithPortNames name [i0, i1] ["i0", "i1", "o"]

insertSemicolons :: [String] -> [String]
insertSemicolons [] = []
insertSemicolons [x] = [x]
insertSemicolons (x:xs) = (x ++ ";") : insertSemicolons xs

insertCommas :: [String] -> [String]
insertCommas [] = []
insertCommas [x] = [x]
insertCommas (x:xs) = (x ++ ",") : insertCommas xs  

--------------------------------------------------------------------------------
-- VHDL packages, entities and architecture.
--------------------------------------------------------------------------------

vhdlPackage :: Bool -> String -> [String] -> [String] -> [String]
vhdlPackage isSeq name inputs outputs
  = ["library ieee;",
    "use ieee.std_logic_1164.all;",
    "package " ++ name ++ "_package is",
    "  component " ++ name ++ " is",
    "    port("] ++
      insertSemicolons (map vhdlInput inputs' ++ map vhdlOutput outputs) ++
    [
    "  );",
    "  end component " ++ name ++ ";",
    "end package " ++ name ++ "_package;"
    ]
    where
    inputs' = if isSeq then
                ["clk", "rst"] ++ inputs
              else
                inputs

vhdlEntity :: Bool -> String -> [String] -> [String] -> [String]
vhdlEntity isSeq name inputs outputs
  = ["library ieee;",
    "use ieee.std_logic_1164.all;",
    "entity " ++ name ++ " is",
    "  port("] ++
    insertSemicolons (map vhdlInput inputs' ++ map vhdlOutput outputs) ++
    [
    "  );",
    "end entity " ++ name ++ ";"
    ]
    where
    inputs' = if isSeq then
                ["clk", "rst"] ++ inputs
              else
                inputs

vhdlArchitecture :: Bool -> String -> Integer -> [String]-> [String]
vhdlArchitecture seqCir name n instances
  = ["library unisim;",
     "use unisim.vcomponents.all;",
     "architecture cava of " ++ name ++ " is",
     "  signal net : std_logic_vector(0 to " ++ show (n-1) ++
        ");",
     "begin",
     "  net(0) <= '0';",
     "  net(1) <= '1';"] ++
     (if seqCir then
        ["  net(2) <= clk;",
         "  net(3) <= rst;"]
      else
        []) ++
     instances ++
    ["end architecture cava ;"
    ]
 
vhdlInput :: String -> String
vhdlInput name = "    signal " ++ name ++ " : in std_ulogic"

vhdlOutput :: String -> String
vhdlOutput name = "    signal " ++ name ++ " : out std_ulogic"
