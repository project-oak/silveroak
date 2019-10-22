{-# LANGUAGE StandaloneDeriving #-}

module AltCava2VHDL where

import Control.Monad.State

import AltCava
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
     (_, netState) = runState (vhdlInstantiation expr NoNet) (initState False)
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

instance Eq NetExpr
instance Show NetExpr

instance Show Coq_cava

data NetlistState
  = NetlistState {netIndex :: Integer,
                  inputs, outputs :: [(String, NetExpr)],
                  vhdlCode :: [String],
                  isSequential :: Bool}
    deriving (Eq, Show)

-- Move NetExpr to the Coq side, then define Rewire constructor
-- for Cava:
--    | Rewire (NetExpr -> NetExpr)
-- to express arbitrary rewirings.

clk :: NetExpr
clk = Net 2

rst :: NetExpr
rst = Net 3

initState :: Bool -> NetlistState
initState isSeq
  = NetlistState (if isSeq then 4 else 2) [] [] [] isSeq

--------------------------------------------------------------------------------
-- vhdlInstantiation walks the Cava circuit expression and elaborates it.
--------------------------------------------------------------------------------

vhdlInstantiation :: Coq_cava -> NetExpr -> State NetlistState NetExpr
vhdlInstantiation (Input name) _
  = do netState <- get
       let o = netIndex netState
           vhdl = vhdlCode netState
           inps = inputs netState
           name' = decodeCoqString name
           assignInput = "  net(" ++ show o ++ ") <= " ++ name' ++ ";"
       put (netState{netIndex = o+1,
                     inputs=(name', Net o):inps,
                     vhdlCode = assignInput:vhdl})
       return (Net o)
vhdlInstantiation Inv i = vhdlUnaryOp "inv" i
vhdlInstantiation And2 (NetPair _ _ i0 i1) = vhdlBinaryOp "and2" i0 i1
vhdlInstantiation Xor2 (NetPair _ _ i0 i1) = vhdlBinaryOp "xor2" i0 i1
vhdlInstantiation Xorcy (NetPair _ _ ci li)
  = vhdlOpWithPortNames "xorcy" [ci, li] ["ci", "li", "o"]
vhdlInstantiation Muxcy (NetPair _ _ s (NetPair _ _ di ci))
  = vhdlOpWithPortNames "muxcy" [s, di, ci] ["s", "di", "ci", "o"]
vhdlInstantiation (Delay _) i
  = do o <- vhdlOpWithPortNames "fdr" [i, clk, rst] ["d", "c", "r", "q"]
       netState <- get
       put (netState{isSequential = True})
       return o
vhdlInstantiation (Compose _ _ _ f g) i
  = do x <- vhdlInstantiation f i
       vhdlInstantiation g x
vhdlInstantiation (Par2 a b c d f g) NoNet
  = vhdlInstantiation (Par2 a b c d f g) (NetPair NoSignal NoSignal NoNet NoNet)
vhdlInstantiation (Par2 _ _ p q f g) (NetPair _ _ a b)
  = do ax <- vhdlInstantiation f a
       bx <- vhdlInstantiation g b
       return (NetPair p q ax bx)          
vhdlInstantiation (Output name) o      
  = do netState <- get
       let outs = outputs netState
           name' = decodeCoqString name
       put (netState{outputs=(name', o):outs})
       return o
vhdlInstantiation (Rewire _ _ f) i = return (f i)

--------------------------------------------------------------------------------
-- showNet displays a net in VHDL syntax.
--------------------------------------------------------------------------------

showNet :: NetExpr -> String
showNet (Net n) = show n
showNet other = error ("Can't emit " ++ show other)

vhdlOpWithPortNames :: String -> [NetExpr] -> [String] ->
                       State NetlistState NetExpr
vhdlOpWithPortNames name instantiatedInputs portNames
  = do netState <- get
       let o = netIndex netState
           vhdl = vhdlCode netState
           inputPorts = zipWith wireUpPort (init portNames) inputNumbers
           allPorts = inputPorts ++ [wireUpPort (last portNames) o]
           inst = "  " ++ name ++ "_" ++ show o ++
                  " : " ++ name ++ " port map (\n" ++
                  unlines (insertCommas allPorts) ++ "  );"
       put (netState{netIndex = o+1, vhdlCode = inst:vhdl})
       return (Net o)
    where
    wireUpPort n i = "    " ++ n ++ " => net(" ++ show i ++ ")"
    inputNumbers = map (\(Net n) -> n) instantiatedInputs

vhdlUnaryOp :: String -> NetExpr -> State NetlistState NetExpr
vhdlUnaryOp name i =
  vhdlOpWithPortNames name [i] ["i", "o"]

vhdlBinaryOp :: String -> NetExpr -> NetExpr -> State NetlistState NetExpr
vhdlBinaryOp name i0 i1
  = vhdlOpWithPortNames name [i0, i1] ["i0", "i1", "o"]

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
