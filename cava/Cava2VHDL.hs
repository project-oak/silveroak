module Cava2VHDL where

import Data.List
import Control.Monad.State

import Cava
import qualified Datatypes
import ExtractionUtils

genVHDL :: String -> [Coq_cava] -> [String]
genVHDL name exprs
  =  vhdlPackage seqCir name circuitInputs circuitOutputs ++ [""] ++
     vhdlEntity seqCir name circuitInputs circuitOutputs ++ [""] ++
     vhdlArchitecture seqCir name (netIndex netState) (vhdlCode netState)
     where
     exprs' = nubBy sameOutputs exprs -- Remove duplicate and forked values.
     (_, netState)
        = runState (sequence (map vhdlInstantiation exprs')) (initState seqCir)
     circuitInputs = nub (concat (map findInputs exprs'))
     circuitOutputs = nub (concat (map findOutputs exprs'))
     seqCir = isSequential netState

sameOutputs :: Coq_cava -> Coq_cava -> Bool
sameOutputs (Output a _) (Output b _)
  = a' == b'
    where
    a' = decodeCoqString a
    b' = decodeCoqString b
sameOutputs _ _ = False

writeVHDL :: String -> Datatypes.Coq_list Coq_cava -> IO ()
writeVHDL name exprs
  = writeFile (name ++ ".vhdl") (unlines (genVHDL name (decodeList exprs)))

findInputs :: Coq_cava -> [String]
findInputs = nub . findInputs'

findInputs' :: Coq_cava -> [String]
findInputs' c =
  case c of
    Inv x -> findInputs' x
    And2 (Datatypes.Coq_pair i0 i1) -> findInputs' i0 ++ findInputs' i1
    Or2  (Datatypes.Coq_pair i0 i1) -> findInputs' i0 ++ findInputs' i1
    Xor2 (Datatypes.Coq_pair i0 i1) -> findInputs' i0 ++ findInputs' i1
    Xorcy (Datatypes.Coq_pair ci li) -> findInputs' ci ++ findInputs' li
    Muxcy (Datatypes.Coq_pair s (Datatypes.Coq_pair di ci))
      -> findInputs' s ++ findInputs' di ++ findInputs' ci
    Fork2 a  -> findInputs' a
    Fst a -> findInputs' a
    Snd a -> findInputs' a
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
    Xor2 (Datatypes.Coq_pair i0 i1) -> findOutputs' i0 ++ findOutputs' i1
    Xorcy (Datatypes.Coq_pair ci li) -> findOutputs' ci ++ findOutputs' li
    Muxcy (Datatypes.Coq_pair s (Datatypes.Coq_pair di ci))
      -> findOutputs' s ++ findOutputs' di ++ findOutputs' ci
    Fork2 a -> findInputs' a
    Fst a -> findOutputs' a
    Snd a -> findOutputs' a
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

insertSemicolons :: [String] -> [String]
insertSemicolons [] = []
insertSemicolons [x] = [x]
insertSemicolons (x:xs) = (x ++ ";") : insertSemicolons xs

insertCommas :: [String] -> [String]
insertCommas [] = []
insertCommas [x] = [x]
insertCommas (x:xs) = (x ++ ",") : insertCommas xs

clk :: NetExpr
clk = Net 2

rst :: NetExpr
rst = Net 3

data NetlistState
  = NetlistState {netIndex :: Int,
                  vhdlCode :: [String],
                  isSequential :: Bool}
    deriving (Eq, Show)

initState :: Bool -> NetlistState
initState isSeq
  = NetlistState (if isSeq then 4 else 2) [] False


data NetExpr
  = Net Int
  | NetPair NetExpr NetExpr
  deriving (Eq, Show)

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

vhdlUnaryOp :: String -> Cava.Coq_cava -> State NetlistState NetExpr
vhdlUnaryOp name i =
  do instantiatedInput <- vhdlInstantiation i
     vhdlOpWithPortNames name [instantiatedInput] ["i", "o"]

vhdlBinaryOp :: String ->
                Datatypes.Coq_prod Cava.Coq_cava Cava.Coq_cava ->
                State NetlistState NetExpr
vhdlBinaryOp name (Datatypes.Coq_pair i0 i1)
  = do instantiatedInputs <- mapM vhdlInstantiation [i0, i1]
       vhdlOpWithPortNames name instantiatedInputs ["i0", "i1", "o"]

vhdlInstantiation :: Coq_cava -> State NetlistState NetExpr
vhdlInstantiation (Inv x) = vhdlUnaryOp "inv" x
vhdlInstantiation (And2 inputs) = vhdlBinaryOp "and2" inputs
vhdlInstantiation (Or2 inputs)  = vhdlBinaryOp "or2" inputs
vhdlInstantiation (Xor2 inputs) = vhdlBinaryOp "xor2" inputs
vhdlInstantiation (Xorcy (Datatypes.Coq_pair ci li))
  = do instantiatedInputs <- mapM vhdlInstantiation [ci, li]
       vhdlOpWithPortNames "xorcy" instantiatedInputs ["ci", "li", "o"]   
vhdlInstantiation (Muxcy (Datatypes.Coq_pair s (Datatypes.Coq_pair di ci)))
  = do instantiatedInputs <- mapM vhdlInstantiation [s, di, ci]
       vhdlOpWithPortNames "muxcy" instantiatedInputs ["s", "di", "ci", "o"]
vhdlInstantiation (Fork2 input)
  = do r <- vhdlInstantiation input
       return (NetPair r r) 
vhdlInstantiation (Fst input)
  = do ab <- vhdlInstantiation input
       let NetPair a _ = ab
       return a
vhdlInstantiation (Snd input)
  = do ab <- vhdlInstantiation input
       let NetPair _ b = ab
       return b                              
vhdlInstantiation (Signal name)
  = do netState <- get
       let o = netIndex netState
           vhdl = vhdlCode netState
           assignment = "  net(" ++ show o ++ ") <= " ++ (decodeCoqString name)
                        ++ ";"
       put (netState{netIndex = o+1, vhdlCode = assignment:vhdl})
       return (Net o)
vhdlInstantiation (Output name expr)
       = do expri <- vhdlInstantiation expr
            netState <- get
            let o = netIndex netState
                vhdl = vhdlCode netState
                assignment = "  " ++ decodeCoqString name ++ " <= net(" ++
                             showNet expri ++ ");";
            put (netState{vhdlCode = assignment:vhdl})
            return (Net o)
vhdlInstantiation (Delay d)
  = do instantiatedInput <- vhdlInstantiation d
       o <- vhdlOpWithPortNames "fdr"
                                 [instantiatedInput, clk, rst]
                                 ["d", "c", "r", "q"]
       netState <- get
       put (netState{isSequential = True})
       return o
                       