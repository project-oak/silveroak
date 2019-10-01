module Cava2VHDL where

import Data.List
import Control.Monad.State

import Cava
import qualified Datatypes
import ExtractionUtils

genVHDL :: String -> Coq_cava -> [String]
genVHDL name expr
  =  vhdlPackage seqCir name circuitInputs circuitOutputs ++ [] ++
     vhdlEntity seqCir name circuitInputs circuitOutputs ++ [] ++
     vhdlArchitecture seqCir name n (vhdlCode instances)
     where
     (n, instances) = runState (vhdlInstantiation expr) (initState seqCir)
     circuitInputs = findInputs expr
     circuitOutputs = findOutputs expr
     seqCir = isSequential instances

writeVHDL :: String -> Coq_cava -> IO ()
writeVHDL name expr = writeFile (name ++ ".vhdl") (unlines (genVHDL name expr))

findInputs :: Coq_cava -> [String]
findInputs = nub . findInputs'

findInputs' :: Coq_cava -> [String]
findInputs' c =
  case c of
    Inv x -> findInputs' x
    And2 (Datatypes.Coq_pair i0 i1) -> findInputs' i0 ++ findInputs' i1
    Or2  (Datatypes.Coq_pair i0 i1) -> findInputs' i0 ++ findInputs' i1
    Delay x -> findInputs' x
    Signal name -> [decodeCoqString name]
    Output _ expr -> findInputs' expr

findOutputs :: Coq_cava -> [String]
findOutputs = nub . findOutputs'
    
findOutputs' :: Coq_cava -> [String]
findOutputs' c =
  case c of
    Inv x -> findOutputs' x
    And2 (Datatypes.Coq_pair i0 i1) -> findOutputs' i0 ++ findOutputs' i1
    Or2  (Datatypes.Coq_pair i0 i1) -> findOutputs' i0 ++ findOutputs' i1
    Delay x -> findInputs' x
    Signal _ -> []
    Output name _ -> [decodeCoqString name]

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

vhdlArchitecture :: Bool -> String -> Int -> [String]-> [String]
vhdlArchitecture seqCir name n instances
  = ["library unisim;",
     "use unisim.vcomponents.all;",
     "architecture cava of " ++ name ++ " is",
     "  signal net : std_logic_vector(" ++ show low ++ " to " ++ show (n-1) ++
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
    where
    low = if seqCir then
            4
          else
            2
 
vhdlInput :: String -> String
vhdlInput name = "    signal " ++ name ++ " : in std_ulogic"

vhdlOutput :: String -> String
vhdlOutput name = "    signal " ++ name ++ " : out std_ulogic"

insertSemicolons :: [String] -> [String]
insertSemicolons [] = []
insertSemicolons [x] = [x]
insertSemicolons (x:xs) = (x ++ ";") : insertSemicolons xs

insertCommas :: [String] -> [String]
insertCommas [] = []
insertCommas [x] = [x]
insertCommas (x:xs) = (x ++ ",") : insertCommas xs

clk :: Int
clk = 2

rst :: Int
rst = 3

data NetlistState
  = NetlistState {netIndex :: Int,
                  vhdlCode :: [String],
                  isSequential :: Bool}
    deriving (Eq, Show)

initState :: Bool -> NetlistState
initState isSeq
  = NetlistState (if isSeq then 4 else 2) [] False

vhdlOpWithPortNames :: String -> [Int] -> [String] ->
                       State NetlistState Int
vhdlOpWithPortNames name instantiatedInputs portNames
  = do state <- get
       let o = netIndex state
           vhdl = vhdlCode state
           inputPorts = zipWith wireUpPort (init portNames) instantiatedInputs
           allPorts = inputPorts ++ [wireUpPort (last portNames) o]
           inst = "  " ++ name ++ "_" ++ show o ++
                  " : " ++ name ++ " port map (\n" ++
                  unlines (insertCommas allPorts) ++ "  );"
       put (state{netIndex = o+1, vhdlCode = inst:vhdl})
       return o
    where
    wireUpPort n i = "    " ++ n ++ " => net(" ++ show i ++ ")"

vhdlUnaryOp :: String -> Cava.Coq_cava -> State NetlistState Int
vhdlUnaryOp name i =
  do instantiatedInput <- vhdlInstantiation i
     vhdlOpWithPortNames name [instantiatedInput] ["i", "o"]

vhdlBinaryOp :: String ->
                Datatypes.Coq_prod Cava.Coq_cava Cava.Coq_cava ->
                State NetlistState Int
vhdlBinaryOp name (Datatypes.Coq_pair i0 i1)
  = do instantiatedInputs <- mapM vhdlInstantiation [i0, i1]
       vhdlOpWithPortNames name instantiatedInputs ["i0", "i1", "o"]

vhdlInstantiation :: Coq_cava -> State NetlistState Int
vhdlInstantiation (Inv x) = vhdlUnaryOp "inv" x
vhdlInstantiation (And2 inputs) = vhdlBinaryOp "and2" inputs
vhdlInstantiation (Or2 inputs)  = vhdlBinaryOp "or2" inputs
vhdlInstantiation (Xor2 inputs)  = vhdlBinaryOp "xor2" inputs
vhdlInstantiation (Signal name)
  = do state <- get
       let o = netIndex state
           vhdl = vhdlCode state
           assignment = "  net(" ++ show o ++ ") <= " ++ (decodeCoqString name)
                        ++ ";"
       put (state{netIndex = o+1, vhdlCode = assignment:vhdl})
       return o
vhdlInstantiation (Output name expr)
       = do expri <- vhdlInstantiation expr
            state <- get
            let o = netIndex state
                vhdl = vhdlCode state
                assignment = "  " ++ decodeCoqString name ++ " <= net(" ++
                             show expri ++ ");";
            put (state{vhdlCode = assignment:vhdl})
            return o
vhdlInstantiation (Delay d)
  = do instantiatedInput <- vhdlInstantiation d
       o <- vhdlOpWithPortNames "fdre"
                                 [instantiatedInput, clk, rst]
                                 ["d", "c", "r", "q"]
       state <- get
       put (state{isSequential = True})
       return o
                         