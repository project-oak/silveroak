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

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecursiveDo #-}


{-

This module explains how overloaded circuit descriptions work
in Lava for both circuit simulation and nelist generation, with
the use of mdo-syntax for capturing the use of MonadFix for bending
wires from the output back to the input.

-}

module Lava
where

import Control.Monad.Identity
import Control.Monad.State

-- The Lava class abstracts over a monad `m` that is based on MonadFix
-- and a type `bit` that represents the values that flow over wires.
-- For circuit simulation `bit` is [Bool], and for netlist generation
-- the `bit` type will be `State NetlistState` which builds up a circuit
-- graph using the state monad.

class MonadFix m => Lava m bit where
  inv :: bit -> m bit          -- invertor
  and2 :: (bit, bit) -> m bit  -- 2-input AND gate
  delay :: bit -> m bit        -- unit delay, with the initial output 0


-- An instance of the Lava class that performs circuit simulation.

instance Lava Identity [Bool] where
  inv x = return (map not x)
  and2 (as, bs) = return [a && b | (a, b) <- zip as bs]
  delay xs = return (False:xs)

-- Some simulation examples.

sim1 :: [Bool]
sim1 = runIdentity $ inv [False, True, True, False]
{-
*Lava> sim1
[True,False,False,True]
-}

sim2 :: [Bool]
sim2 = runIdentity $
       and2 ([False, True,  False, True],
             [False, False, True,  True]
            )
{-
*Lava> sim2
[False,False,False,True]
-}

-- Now let's make a circuit graph, where the circuit components
-- are the nodes of the graph and the edges of the graph are wires
-- identified by integer values. A circuit graph is simply a list
-- of `Component`s.

data Component
  = INV Int Int
  | AND2 Int Int Int
  | DELAY Int Int
  deriving (Eq, Show)

-- The state required to build up the circuit graph is simply the
-- next available netlist number and the circuit graph.

data NetlistState
  = NetlistState Int [Component]
    deriving (Eq, Show)

-- A NAND gate is wired up with the incoming wire `i` and the
-- fresh new net number `o` is used for the output, and this
-- net number is also returned as the result, the the net number
-- in the state is bumped by one to account for the consumption of
-- one net number wire for the output.

invGate :: Int -> State NetlistState Int
invGate i
  = do NetlistState o components <- get
       put (NetlistState (o+1) ((INV i o):components))
       return o

-- and2Gate: same pattern as the NAND gate.

and2Gate :: (Int, Int) -> State NetlistState Int
and2Gate (i0, i1)
  = do NetlistState o components <- get
       put (NetlistState (o+1) ((AND2 i0 i1 o):components))
       return o

-- delayGate: same pattern as the NAND gate.

delayGate :: Int -> State NetlistState Int
delayGate i
  = do NetlistState o components <- get
       put (NetlistState (o+1) ((DELAY i o):components))
       return o

-- Now we can create an instance of Lava for netlist generation.

instance Lava (State NetlistState) Int where
  inv = invGate
  and2 = and2Gate
  delay = delayGate               

-- An example of a nandGate composed with a left-to-right composition of
-- Kleisli arrows.

nandGate :: Lava m bit => (bit, bit) -> m bit
nandGate = and2 >=> inv

sim3 :: [Bool]
sim3 = runIdentity $
       nandGate ([False, True,  False, True],
                 [False, False, True,  True]
                )
{-
*Lava> sim3
[True,True,True,False]
-}

-- Produce a netlist for the NAND gate. When we evaluate it we
-- see a circuit graph where the AND gate has inputs 0 and 1 and 
-- produces an output 2, and the INV gate takes the 2 wire and inverts
-- it to produce an output result on the 3 wire.

nandGateNetlist :: NetlistState
nandGateNetlist = execState (nandGate (0::Int, 1)) (NetlistState 2 [])
{-
*Lava> nandGateNetlist
NetlistState 4 [INV 2 3,AND2 0 1 2
-}


{-

-- Define a loop combinator to bend the select element of a pair to
-- pair circuit to allow us to express feedback loops for sequential circuits.

   ------------
  |    ----    |
  |-->|    |---  C (looped back)
      |    |
  A ->|    | -> B
       ----


-}

loop :: MonadFix m => ((a, c) -> m (b, c)) -> a -> m b
loop circuit a
  = mdo (b, c) <- circuit (a, c)
        return b

-- Another handy combinator for forking a wire.

fork :: Monad m => a -> m (a, a)
fork a = return (a, a)


-- A silly sequential circuit with feedback: a NAND gate with its
-- output forked, one fork is feed back by the loop, the other fork
-- forms the output of the circuit.

loopedNAND :: Lava m bit => bit -> m bit
loopedNAND = loop (nandGate >=> delay >=> fork)

sim4 :: [Bool]
sim4 = runIdentity $ loopedNAND [False, True, True, False]

{-
*Lava> sim4
[False,True,False,True,True]
-}

loopedNANDNetlist :: NetlistState
loopedNANDNetlist = execState (loopedNAND (0::Int)) (NetlistState 1 [])

-- Note how the fed-back wire is correctly represented in the graph i.e.
-- the output of the DELAY component is wire, and this wire is feb back
-- to the second input of the AND2 gate.
{-
*Lava> loopedNANDNetlist
NetlistState 4 [DELAY 2 3,INV 1 2,AND2 0 3 1]
-}

-- Even for an infinte input, we can ask for a finite portion
-- of the output.        

sim5 :: [Bool]
sim5 = take 6 $ runIdentity $ loopedNAND (repeat True)
{-
*Lava> sim5
[False,True,False,True,False,True]
-}

loopMF' :: MonadFix m => ((a, c) -> m (b, c)) -> a -> m (b, c)
loopMF' circuit a
  = mfix (\bc -> do (b, c') <- circuit (a, snd bc)
                    return (undefined, c'))

loopMF :: MonadFix m => ((a, c) -> m (b, c)) -> a -> m b
loopMF circuit a
  = do (b, _) <- loopMF' circuit a 
       return b

loopedMFNAND :: Lava m bit => bit -> m bit
loopedMFNAND = loopMF (nandGate >=> delay >=> fork)

loopedMFNANDNetlist :: NetlistState
loopedMFNANDNetlist = execState (loopedMFNAND (0::Int)) (NetlistState 1 [])
{-
*Lava> loopedMFNANDNetlist
NetlistState 4 [DELAY 2 3,INV 1 2,AND2 0 3 1]
-}