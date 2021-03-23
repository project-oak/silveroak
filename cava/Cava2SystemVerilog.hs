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

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}

module Cava2SystemVerilog (module Cava2SystemVerilog, module TestBench)
where

import Control.Monad.State.Lazy
import Numeric
import qualified Vector

import GHC.Types (Any)

import qualified BinNums
import Netlist
import Signal
import qualified StateMonad

import SystemVerilogUtils

import TestBench

{-
NOTES.
======
The current SystemVerilog extraction process only generates packed arrays.
All arrays are interpretated as having "downto" indexing e.g. [3:0].
An attempt is made to unsmash literals to recover stems of arrays.
-}

writeSystemVerilog :: CavaState -> IO ()
writeSystemVerilog cavastate@(Netlist.Coq_mkCavaState _ _ _ _
                    _ _ _ _ _ libs)
  = do putStr ("Generating " ++ filename ++ "...")
       writeFile filename ("// Cava auto-generated SystemVerilog. Do not hand edit.\n")
       sequence_ [appendFile filename (unlines (cava2SystemVerilog (swapIn m cavastate))) | (_, m) <- libs]
       appendFile filename (unlines (cava2SystemVerilog cavastate))
       putStrLn (" [done]")
    where
    filename = Netlist.moduleName (Netlist.coq_module cavastate) ++ ".sv"


swapIn :: Netlist.Module -> CavaState -> CavaState
swapIn m cavaState@(Netlist.Coq_mkCavaState netNumber vCount' vDefs' ext'
                    clk clkEdge rst rstEdge _ _)
  = Netlist.Coq_mkCavaState netNumber vCount' vDefs' ext'
                    clk clkEdge rst rstEdge m []

fromN :: BinNums.N -> Integer
fromN bn
  = case bn of
      BinNums.N0 -> 0
      BinNums.Npos n -> n

cava2SystemVerilog :: Netlist.CavaState -> [String]
cava2SystemVerilog cavaState@(Netlist.Coq_mkCavaState netNumber vCount' vDefs' ext'
                    clk clkEdge rst rstEdge
                    (Netlist.Coq_mkModule moduleName instances'
                    inputs outputs) libs)
  = ["module " ++ moduleName ++ "("] ++

    insertCommas (inputPorts inputs ++ outputPorts outputs) ++
    ["  );"] ++
    ["",
     "  timeunit 1ns; timeprecision 1ns;",
     ""] ++
    declareLocalNets (fromN netNumber) ++
    [vectorDeclaration ("v" ++ show i) k s ++ ";" | ((k, s), i) <- zip vDefs [0..]] ++
    [ "  " ++ t ++ " ext_" ++ show i ++ ";" | (t, i) <- zip ext [0..]] ++
    [""] ++
    [generateInstance genState inst i | (inst, i) <- zip instances [0..]] ++
    [""] ++
    ["endmodule",
     ""]
    where
    genState = NetlistGenerationState clk clkEdge rst rstEdge
    (instances'', Netlist.Coq_mkCavaState _ vCount vDefs ext
                  _ _ _ _
                  (Netlist.Coq_mkModule _ assignInstances
                  _ _) _)
      = runState (unsmashSignalInstances instances')
          (Netlist.Coq_mkCavaState netNumber vCount' vDefs' ext'
                    clk clkEdge rst rstEdge
                    (Netlist.Coq_mkModule moduleName []
                    inputs outputs) libs)
    instances = instances'' ++ assignInstances

declareLocalNets :: Integer -> [String]
declareLocalNets n
  = if n == 0 then
      []
    else
      ["  logic net[0:" ++ show (n-1) ++ "];"]

data NetlistGenerationState
  = NetlistGenerationState (Maybe Signal) SignalEdge (Maybe Signal) SignalEdge

inputPorts :: [Netlist.PortDeclaration] -> [String]
inputPorts = map inputPort

inputPort :: Netlist.PortDeclaration -> String
inputPort (Coq_mkPort name typ)
  = "  input " ++ declareSignal name typ

outputPorts :: [Netlist.PortDeclaration] -> [String]
outputPorts = map outputPort

outputPort :: Netlist.PortDeclaration -> String
outputPort (Netlist.Coq_mkPort name typ)
  = "  output " ++ declareSignal name typ

showVectorElements :: [Signal] -> String
showVectorElements e
  = concat (insertCommas (map showSignal e))


isGndOrVcc :: Signal -> Bool
isGndOrVcc Gnd = True
isGndOrVcc Vcc = True
isGndOrVcc _ = False

gndVccListToInt :: [Signal] -> Int
gndVccListToInt [] = 0
gndVccListToInt (Gnd:xs) = 2 * gndVccListToInt xs
gndVccListToInt (Vcc:xs) = 1 + 2 * gndVccListToInt xs

bvConst :: [Signal] -> String
bvConst bv
  = show (length bv) ++ "'h" ++ showHex (gndVccListToInt bv) ""

-- Show vector literals, interpretating them as packed arrays
-- with downto indexing.
showVecLiteral :: SignalType -> [Signal] -> String
showVecLiteral k e
  = case k of
      Bit -> if all isGndOrVcc e then  -- special case for bit-vector constants
               bvConst e
             else
              -- Vector, downto indexing
              "{" ++ showVectorElements (reverse e) ++ "}"
      _   -> -- Vector, downto indexing
             "{" ++ showVectorElements (reverse e) ++ "}"

showSignal :: Signal -> String
showSignal signal
  = case signal of
      UndefinedSignal -> error "Attempt to use an undefined signal"
      UninterpretedSignal _ name -> name
      UninterpretedSignalIndex _ i -> "ext_" ++ show (fromN i)
      SelectField _ _ sk1 f -> showSignal sk1 ++ "." ++ f
      Gnd -> "1'b0"
      Vcc -> "1'b1"
      Wire n -> "net[" ++ show (fromN n) ++ "]"
      NamedWire name -> name
      NamedVector _ _ name -> name
      LocalVec _ _ v -> "v" ++ show (fromN v)
      VecLit k s vs -> showVecLiteral k (Vector.to_list s vs)
      IndexAt _ _ _ v i -> showSignal v ++ "[" ++ showSignal i ++ "]"
      IndexConst _ _ v i -> showSignal v ++ "[" ++ show i ++ "]"
      Slice k _ start len v -> showSignal v ++ showSliceIndex k start len
      UnsignedAdd _ _ _ a b -> "(" ++ showSignal a ++ " + " ++ showSignal b ++ ")"
      UnsignedSubtract _ _ _ a b -> "(" ++ showSignal a ++ " - " ++ showSignal b ++ ")"
      UnsignedMultiply _ _ _ a b -> "(" ++ showSignal a ++ " * " ++ showSignal b ++ ")"
      GreaterThanOrEqual _ _ a b -> "(" ++ showSignal a ++ " >= " ++ showSignal b ++ ")"

simplifySignal :: Signal -> Signal
-- TODO: Consider adding other compile time evaluations e.g. for IndexConst.
simplifySignal s = s

showSliceIndex :: SignalType -> Integer -> Integer -> String
showSliceIndex k start len
  = case k of
      Bit -> "[" ++ show top ++ ":" ++ show start ++ "]"
      Vec _ _ -> "[" ++ show start ++ ":" ++ show top ++ "]"
    where
    top = start + len - 1

--------------------------------------------------------------------------------
-- Generate SystemVerilog for a specific instance.
--------------------------------------------------------------------------------

generateInstance :: NetlistGenerationState -> Instance -> Int -> String
generateInstance netlistState (Delay t initV d o) _
  = unlines [
    "  always_ff @(" ++ showEdge clkEdge ++ " " ++ showSignal clk ++ " or "
                     ++ showEdge rstEdge ++ " " ++ showSignal rst ++ ") begin",
    "    if (" ++ negReset ++ showSignal rst ++ ") begin",
    "      " ++ showSignal o ++ " <= " ++ showCombExpr t initV ++ ";",
    "    end else begin",
    "      " ++ showSignal o ++ " <= " ++ showSignal d ++ ";",
    "    end",
    "  end"]
    where
    NetlistGenerationState (Just clk) clkEdge (Just rst) rstEdge = netlistState
    showEdge edge = case edge of
                      PositiveEdge -> "posedge"
                      NegativeEdge -> "negedge"
    negReset = case rstEdge of
                 PositiveEdge -> ""
                 NegativeEdge -> "!"
generateInstance netlistState (DelayEnable t initV en d o) _
  = unlines [
    "  always_ff @(" ++ showEdge clkEdge ++ " " ++ showSignal clk ++ " or "
                     ++ showEdge rstEdge ++ " " ++ showSignal rst ++ ") begin",
    "    if (" ++ negReset ++ showSignal rst ++ ") begin",
    "      " ++ showSignal o ++ " <= " ++ showCombExpr t initV ++ ";",
    "    end else",
    "      if (" ++ showSignal en ++ ") begin",
    "        " ++ showSignal o ++ " <= " ++ showSignal d ++ ";",
    "    end",
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
generateInstance _ (Component name parameters connections) instNr =
  mkInstance name parameters connections' instNr
  where
  connections' = [(n, extractSignal us) | (n, us) <- connections]

primitiveInstance :: String -> [Signal] -> Int -> String
primitiveInstance instName args instNr
  = "  " ++ instName ++ " inst" ++ "_" ++ show instNr ++ " " ++
    showArgs args ++ ";"

showArgs :: [Signal] -> String
showArgs args = "(" ++ concat (insertCommas (map showSignal args)) ++ ")"

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
showPortArgs args = "(" ++ concat (insertCommas (map showPortArg args)) ++ ")"

showPortArg :: (String, Signal) -> String
showPortArg (p, n) = "." ++ p ++ "(" ++ showSignal n ++ ")"

showParameters :: [(String, ConstExpr)] -> String
showParameters parameters
  = " #(" ++ concat (insertCommas (map showParameter parameters)) ++ ")"

showParameter :: (String, ConstExpr) -> String
showParameter (name, constExpr)
  = "." ++ name ++ "(" ++ showConstExpr constExpr ++ ")"

showConstExpr :: ConstExpr -> String
showConstExpr constExpr =
  case constExpr of
    HexLiteral w v -> show w ++ "'h" ++ showHex (fromN v) ""
    StringLiteral s -> "\"" ++ s ++ "\""

showCombExpr :: SignalType -> GHC.Types.Any -> String
showCombExpr t expr
  = case t of
      Bit -> showBool ((Signal.unsafeCoerce expr)::Bool)
      Vec t2 s -> showCVec t2 (Vector.to_list s ((Signal.unsafeCoerce expr)::Vector.Coq_t t))

showBool :: Bool -> String
showBool False = "1'b0"
showBool True = "1'b1"

showCVec :: SignalType -> [GHC.Types.Any] -> String
showCVec t x
  = "{" ++ concat (insertCommas (map (showCombExpr t) x)) ++ "}"

--------------------------------------------------------------------------------
-- unsmashSignaling vector literals.
--------------------------------------------------------------------------------

deriving instance Eq BinNums.N
deriving instance Eq SignalType
deriving instance Eq (Vector.Coq_t Signal)
deriving instance Eq Signal

-- Show instances for debugging.
deriving instance Show Signal
deriving instance Show (Vector.Coq_t Signal)
deriving instance Show BinNums.N

unsmashSignalInstance :: Instance -> State CavaState Instance
unsmashSignalInstance = mapSignalsInInstanceM unsmashSignal

unsmashSignalInstances :: [Instance] -> State CavaState [Instance]
unsmashSignalInstances instances =
  sequence (map unsmashSignalInstance instances)

mapSignalsInInstanceM :: (Signal -> State CavaState Signal) ->
                          Instance -> State CavaState Instance
mapSignalsInInstanceM f inst
  = case inst of
      Not i o -> do fi <- f i
                    fo <- f o
                    return (Not fi fo)
      And i0 i1 o -> do fi0 <- f i0
                        fi1 <- f i1
                        fo  <- f o
                        return (And fi0 fi1 fo)
      Nand i0 i1 o -> do fi0 <- f i0
                         fi1 <- f i1
                         fo  <- f o
                         return (Nand fi0 fi1 fo)
      Or i0 i1 o -> do fi0 <- f i0
                       fi1 <- f i1
                       fo  <- f o
                       return (Or fi0 fi1 fo)
      Nor i0 i1 o -> do fi0 <- f i0
                        fi1 <- f i1
                        fo  <- f o
                        return (Nor fi0 fi1 fo)
      Xor i0 i1 o -> do fi0 <- f i0
                        fi1 <- f i1
                        fo  <- f o
                        return (Xor fi0 fi1 fo)
      Xnor i0 i1 o -> do fi0 <- f i0
                         fi1 <- f i1
                         fo  <- f o
                         return (Xnor fi0 fi1 fo)
      Buf i o -> do fi <- f i
                    fo <- f o
                    return (Buf fi fo)
      Delay t initV d o -> do fd <- f d
                              fo <- f o
                              return (Delay t initV fd fo)
      DelayEnable t initV en d o -> do fd <- f d
                                       fen <- f en
                                       fo <- f o
                                       return (DelayEnable t initV fen fd fo)
      AssignSignal k t v -> do ft <- f t
                               fv <- f v
                               return (AssignSignal k ft fv)
      Component name args vals ->
        do let sigs = map (extractSignal . snd) vals
           sigs' <- sequence (map f sigs)
           return (Component name args (zip (map fst vals) (map untypeSignal sigs')))

--------------------------------------------------------------------------------
-- Extract Signal from UntypedSignal
extractSignal :: UntypedSignal -> Signal
extractSignal (USignal _ s) = s

-- Convert back to UntypedSignal
untypeSignal :: Signal -> UntypedSignal
untypeSignal sig = USignal Void sig

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Check for contiguous static indexing to identify vector slices.
--------------------------------------------------------------------------------

checkIndexes :: SignalType -> Integer -> Integer -> Signal -> Integer -> [Signal] -> Maybe Signal
checkIndexes k fullSize startingIndex stem currentIndex []
  = Just (Slice k fullSize startingIndex (currentIndex - startingIndex) stem)
checkIndexes k fullSize startingIndex stem currentIndex (s:sx)
  = case s of
      IndexConst k sz v2 i -> if currentIndex == i && stem == v2 then
                                checkIndexes k sz startingIndex stem (currentIndex+1) sx
                              else
                                Nothing
      _ -> Nothing

checkStem :: SignalType -> Integer -> [Signal] -> Maybe Signal
checkStem k sz [] = Nothing
checkStem k sz (v:vs)
  = case v of
      IndexConst k2 s2 v2 startingIndex ->
       case k of
          Bit        -> checkIndexes k s2 startingIndex v2 (startingIndex+1) vs
          Vec _ _ -> checkIndexes k s2 startingIndex v2 (startingIndex+1) vs
      _ -> Nothing

-- If a slice contains just one element, just return a static index to that
-- element. If a slice is indexing the whole vector, just return the vector
-- stem.
fullSlice ::  Signal -> Signal
fullSlice (Slice k s startingIndex 1 stem) = IndexConst k s stem startingIndex
fullSlice s@(Slice _ fullLen startingIndex len stem)
  = if fullLen == len then
      stem
    else
      s

-- Recover slices and whole vector stems and look for places where a vector
-- literal is not legal and re-write by creating a fresh vector name.
unsmashSignal :: Signal -> State CavaState Signal
unsmashSignal signal
  = case signal of
      VecLit k s v -> do uv <- sequence (map unsmashSignal (Vector.to_list s v))
                         case checkStem k s uv  of
                           Just stem -> return (fullSlice stem)
                           Nothing -> return (VecLit k s (Vector.of_list uv))
      IndexAt k sz isz v i -> do uv <- unsmashSignal v
                                 fv <- freshen uv -- The vector to be indexed can't be a vector literal
                                 ui <- unsmashSignal i
                                 return (IndexAt k sz isz fv ui)
      IndexConst k s v i -> do uv <- unsmashSignal v
                               fv <- freshen uv -- The vector to be indexed can't be a vector literal
                               return (IndexConst k s fv i)
      SelectField k1 k2 sk1 f -> do usk1 <- unsmashSignal sk1
                                    return (SelectField k1 k2 usk1 f)
      Slice k s startAt len v -> do uv <- unsmashSignal v
                                    fv <- freshen uv -- The slice to be indexed can't be a vector literal
                                    return (Slice k s startAt len fv)
      _ -> return signal

-- If a signal is a vector literal, give it a name and return that name.
-- Used to rewrite vector literals in locations where they are not allowed
-- or in places where very large long lines would get generated.
freshen :: Signal -> State CavaState Signal
freshen signal
  = case signal of
      VecLit k s v -> do freshV <- freshVector k s
                         addAssignment (Vec k s) freshV (VecLit k s v)
                         return freshV
      IndexAt k sz isz v i -> do vf <- freshen v
                                 return (IndexAt k sz isz vf i)
      _ -> return signal

-- Add an assignment to the context to store new vector names induced by
-- the fresh transformation.
addAssignment :: SignalType -> Signal -> Signal -> State CavaState ()
addAssignment k a b
  = do Netlist.Coq_mkCavaState netNumber vCount vDefs ext
                    clk clkEdge rst rstEdge
                    (Netlist.Coq_mkModule moduleName instances
                    inputs outputs) libs <- get
       put (Netlist.Coq_mkCavaState netNumber vCount vDefs ext
                    clk clkEdge rst rstEdge
                    (Netlist.Coq_mkModule moduleName ((AssignSignal k a b):instances)
                    inputs outputs) libs)

-- Declare a new local vector and return it as a signal.
freshVector :: SignalType -> Integer -> State CavaState Signal
freshVector k s
  = do Netlist.Coq_mkCavaState netNumber vCount vDefs ext
                    clk clkEdge rst rstEdge
                    (Netlist.Coq_mkModule moduleName instances
                    inputs outputs) libs <- get
       put (Netlist.Coq_mkCavaState netNumber (incN vCount) (vDefs++[(k, s)]) ext
                    clk clkEdge rst rstEdge
                    (Netlist.Coq_mkModule moduleName instances
                    inputs outputs) libs)
       return (LocalVec k s vCount)
