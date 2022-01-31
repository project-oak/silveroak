(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License")           *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(*     http://www.apache.org/licenses/LICENSE-2.0                           *)
(*                                                                          *)
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)

Require Import Coq.Strings.Ascii Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.MonadState.

Require Import Coq.Numbers.DecimalString.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope type_scope.

(* 
This is an experimental version of Cava which illustrates the
type of API I would ideally like to have for Cava for describing
circuits with feedback.
*)

(*
There are two types of wires: single wires that carry one bit of
information which are represented by Bit and a 32-bit unsigned
wire which is represented by Nat.
*)
Inductive SignalType :=
  | Bit : SignalType 
  | Nat : SignalType.


(*
A typeclass let's us write over-loaded circuit descriptions which
can have many instantiations e.g. one for circuit semantics (by way
of similation) and another for generating a circuit netlist. A circuit
will always be a Gallina function which returns its output result
in some instance of a Monad type. We can then compose overloaded
circuit descriptions using the Kleisli arrow >=> and all the other monad
combinators. A very partial API, just enough to make some illustrative examples.
*)
Class Acorn acorn `{Monad acorn} (signal : SignalType -> Type) := {
  (* An invertor gate. *)
  inv : signal Bit -> acorn (signal Bit); 
  (* A NAND gate *)
  and2 : signal Bit * signal Bit -> acorn (signal Bit); 
  (* Add two nat values and then mod by a nat *)
  addMod : nat -> signal Nat * signal Nat -> acorn (signal Nat);
  (* Delay a wire of nat values by one clock cycle. *)
  natDelay : signal Nat -> acorn (signal Nat);
  (* Lava type loop combinator for feedback *)
  loop : (signal Nat * signal Nat -> acorn (signal Nat * signal Nat)) -> 
         signal Nat -> acorn (signal Nat);
  (* Ideally an infinite source of some nat value *)
  constNat : nat -> acorn (signal Nat);
  (* True if the first value is > to the second value. *)
  comparator : signal Nat * signal Nat -> acorn (signal Bit); 
  (* If bool select signal is true then mux2 the first value in the pair, otherwise second element is returned *)
  mux2 : signal Bit * (signal Nat * signal Nat) -> acorn (signal Nat); 
}.

(* Some useful circuit combinators and an example circuit. *)

Section WithAcorn.
  Context  {acorn} {signal} `{Acorn acorn signal}.

  (* Take a wire and fork it into two branches. *)
  Definition fork2 {t : SignalType}
              (a : signal t) : acorn (signal t * signal t) :=
    ret (a, a).

  (* Take a pair input and apply the circuit r to just the first element. *)
  Definition fsT {t1 t2 t3 : SignalType}
            (f : signal t1 -> acorn (signal t3))
            (ab : signal t1 * signal t2) : acorn (signal t3 * signal t2) :=
    let (a, b) := ab in
    o <- f a ;;
    ret (o, b).

  (* Take a pair input and apply the circuit r to just the second element. *)
  Definition snD {t1 t2 t3 : SignalType}
            (f : signal t2 -> acorn (signal t3))
            (ab : signal t1 * signal t2) : acorn (signal t1 * signal t3) :=
    let (a, b) := ab in
    o <- f b ;;
    ret (a, o).

  (* A circuit which delays the second element of a pair and then performs
     a 256-bit addition of the two values in the pair. *)
  Definition circuit1 : signal Nat * signal Nat -> acorn (signal Nat) :=
    snD natDelay >=> addMod 256.

End WithAcorn.

(*
So far we have overloaded circuit descriptions and combinators, but we can't
yet do anything with them until we define some instances of the Acorn class.
Let's create an instance for the simulation of these overloaded circuit descriptions,
which acts as the semantics for these circuits.
*)

(*
We need to explain how to map a SignalType to the types we use to represent the
types of the values that flow over wires. For simulation, Bit will be represented
by a list of bool values, Nat will be represented by a list of nat values.
*)
Definition simulationSignal (t: SignalType) : Type :=
  match t with
  | Bit => list bool
  | Nat => list nat
  end.

(*
Semantics of addition followed by mod. The modBy value is a compile
time constant.
*)
Definition addModSim (modBy : nat) (ab : list nat * list nat) : ident (list nat) :=
  let (a, b) := ab in
  ret (map (fun '(x, y) => (x + y) mod modBy) (combine a b)).

(* Semantics of the two-input comparator. *)
Definition comparatorSim (ab : list nat * list nat) : ident (list bool) :=
  let (a, b) := ab in
  ret (map (fun '(x, y) => y <=? x) (combine a b)).

(* Core semantics of a 2-input multiplexor. *)
Definition mux2' (sxy : bool * (nat * nat)) : nat :=
  let (s, xy) := sxy in
  let (x, y) := xy in
  if s then x else y.

(*
An instance of the Acorn class for circuit simulation, with a dummy value
for loop (since I don't know how to define it) and a hacky definition for
constNat because I don't know how to make an infinite list.
*)
Instance AcornSimulation : Acorn ident simulationSignal := {
  inv i := ret (map negb i);
  and2 '(a, b) := ret (map (fun '(x, y) => andb x y) (combine a b));
  addMod := addModSim;
  natDelay i := ret (0 :: i);
  loop f i := ret i; (* Dummy Definition. QUESTION: How to do this in Coq? cd. how it is done in Lava in Haskell *)
  constNat n := ret (repeat n 100); (* Hack, just repeat n 100 times. How to get an infinite list in Coq? *)
  comparator := comparatorSim;
  mux2 '(sel, (a, b)) := ret (map mux2' (combine sel (combine a b)));
}.

(* We can easily simulate circuits without loops, even if they contain delay elements. *)
Compute (unIdent (circuit1 ([17; 78; 12], [42; 62; 5]))).
(*
	 = [17; 120; 74]
*)

(* What's we can't do is simulate circuits with loop. *)

(*
We can create circuit netlists for circuits with loops. To make a circuit
netlist we first define some types for representing a circuit netlist.
*)

(* The nodes of the circuit graph. *)
Inductive Instance :=
| Inv : N -> N -> N -> Instance
| And2 : N -> N -> N -> N -> Instance
| AddMod : nat -> N -> N -> N -> Instance
| NatDelay : N -> N -> Instance
| AssignNat : N -> N -> Instance
| ConstNat : N -> N -> Instance
| Comparator : N -> N -> N -> Instance
| Mux2 : N -> N -> N -> N -> Instance.

(* The I/O interface of the circuit. *)
Inductive Port :=
| InputBit : string -> N -> Port
| OutputBit : N -> string -> Port
| InputNat : string -> N -> Port
| OutputNat : N -> string -> Port.

(* The complete netlist type. *)
Record Netlist := mkNetlist {
  netlistName : string; (* Name of the module to be generated. *)
  instCount : N; (* A count of the number of nodes. *)
  bitCount : N; (* A count of the number of local bit-type wires. *)
  natCount : N; (* A count of the number of nat-type wires. *)
  instances : list Instance; (* A list of the circuit graph nodes. *)
  ports : list Port; (* The I/O interface of the circuit. *)
}.

(* An empty netlist. *)
Definition emptyNetist : Netlist :=
  mkNetlist "" 0 0 0 [] [].

(*
The types of the values that flow over wires for the netlist
representation is the Signal type which is a symbolic representation
for the value on that wire (the name of a net).
*)
Inductive Signal : SignalType -> Type :=
| BitNet : N -> Signal Bit
| NatNet : N -> Signal Nat.

(* The denotion of a SignalType for netlist generation is just the Signal type. *)
Definition denoteSignal (t: SignalType) : Type := Signal t.

(* Some useful functions for working over netlists. *)

Definition newWire : state Netlist (Signal Bit) :=
  ns <- get ;;
  match ns with
  | mkNetlist name ic bc nc is ps =>
      put (mkNetlist name ic (bc + 1) nc is ps) ;;
      ret (BitNet bc)
  end.

Definition newNat : state Netlist (Signal Nat) :=
  ns <- get ;;
  match ns with
  | mkNetlist name ic bc nc is ps =>
      put (mkNetlist name ic bc (nc + 1) is ps) ;;
      ret (NatNet nc)
  end.

Definition newInstNr : state Netlist N :=
  ns <- get ;;
  match ns with
  | mkNetlist name ic bc nc is ps =>
      put (mkNetlist name (ic + 1) bc nc is ps) ;;
      ret ic
  end.

Definition addInstance (inst : Instance) : state Netlist unit :=
  ns <- get ;;
  match ns with
  | mkNetlist name ic bc nc is ps =>
      put (mkNetlist name ic bc nc (inst::is) ps)
  end.

Definition addPort (p : Port) : state Netlist unit :=
  ns <- get ;;
  match ns with
  | mkNetlist name ic bc nc is ps =>
      put (mkNetlist name ic bc nc is (p::ps))
  end.

Definition wireNr (w : Signal Bit) : N :=
  match w with
  | BitNet n => n
  end.

Definition invGate (i : Signal Bit) : state Netlist (Signal Bit) :=
  o <- newWire ;;
  instNr <- newInstNr ;;
  addInstance (Inv instNr (wireNr i) (wireNr o)) ;;
  ret o.
  
Definition and2Gate (i0i1 : Signal Bit * Signal Bit) : state Netlist (Signal Bit) :=
  o <- newWire ;;
  instNr <- newInstNr ;;
  let (i0, i1) := i0i1 in
  addInstance (And2 instNr (wireNr i0) (wireNr i1) (wireNr o)) ;;
  ret o.

Definition natWireNr (w : Signal Nat) : N :=
  match w with
  | NatNet n => n
  end.

Definition natDelayDef (i : Signal Nat) : state Netlist (Signal Nat) :=
  o <- newNat ;;
  addInstance (NatDelay (natWireNr i) (natWireNr o)) ;;
  ret o.

Definition addModCircuit (modBy : nat) (i0i1 : Signal Nat * Signal Nat) : state Netlist (Signal Nat) :=
  o <- newNat ;;
  let (i0, i1) := i0i1 in
  addInstance (AddMod modBy (natWireNr i0) (natWireNr i1) (natWireNr o)) ;;
  ret o.

(* 
Note that loop is no problem for the netlist instance. We can "bend the wire" to create
a loop by creating a new wire b, using this to drive the input of the body circuit, and then
connect the second output of the body pair result, and fuse it with b to create a feedback loop
i.e. assign b := d.
*)
Definition loopNet (body : Signal Nat * Signal Nat -> state Netlist (Signal Nat * Signal Nat))
                   (a : Signal Nat) : state Netlist (Signal Nat) :=
  b <- newNat ;;
  cd <- body (a, b) ;;
  let '(c, d) := cd in
  addInstance (AssignNat (natWireNr b) (natWireNr d)) ;;
  ret c.

Definition constNatNet (n : nat) : state Netlist (Signal Nat) :=
  x <- newNat ;;
  addInstance (ConstNat (natWireNr x) (N.of_nat n)) ;;
  ret x.

Definition comparatorNet (ab : Signal Nat * Signal Nat) : state Netlist (Signal Bit) :=
  cf <- newWire ;;
  let (a, b) := ab in
  addInstance (Comparator (natWireNr a) (natWireNr b) (wireNr cf)) ;;
  ret cf.

Definition mux2Net (selab : Signal Bit * (Signal Nat * Signal Nat)) : state Netlist (Signal Nat) :=
   let (sel, ab) := selab in
   let (a, b) := ab in
   o <- newNat ;;
   addInstance (Mux2 (wireNr sel) (natWireNr a) (natWireNr b) (natWireNr o)) ;;
   ret o.

(*
The netlist instance for Acorn plugs in the definitions above for creating
a circuit netlist using the stat monad as we go along.
*)
Instance AcornNetlist : Acorn (state Netlist) denoteSignal := {
  inv := invGate;
  and2 := and2Gate;
  addMod := addModCircuit;
  natDelay := natDelayDef;
  loop  := loopNet;
  constNat := constNatNet;
  comparator := comparatorNet;
  mux2 := mux2Net;
}.

(*
Netlist functions for I/O ports which are only available for the
netlist interpretation.
*)

Definition inputBit (name : string) : state Netlist (Signal Bit) :=
  o <- newWire ;;
  addPort (InputBit name (wireNr o)) ;;
  ret o.

Definition outputBit (driver : Signal Bit) (name : string) : state Netlist unit :=
  addPort (OutputBit (wireNr driver) name).

Definition inputNat (name : string) : state Netlist (Signal Nat) :=
  o <- newNat ;;
  addPort (InputNat name (natWireNr o)) ;;
  ret o.

Definition outputNat (driver : Signal Nat) (name : string) : state Netlist unit :=
  addPort (OutputNat (natWireNr driver) name).

(* Declare the name of a circuit. *)
Definition setCircuitName (name : string) : state Netlist unit :=
  ns <- get ;;
  match ns with
  | mkNetlist _ ic bc nc is ps =>
      put (mkNetlist name ic bc nc is ps)
  end.

(* Generate a netlist from a circuit name and a circuit graph. *)
Definition netlist (name : string) (circuit : state Netlist unit) : Netlist :=
  execState (setCircuitName name ;; circuit) emptyNetist.

(* Generate the SystemVerilog string from the netlist data-type. *)
Local Open Scope string_scope.

Fixpoint insertCommas (lines : list string) : string :=
  match lines with
  | [] => ""
  | [x] => x
  | x::xs => x ++ ", " ++ insertCommas xs
  end.

Definition portDeclaration (p : Port) : string :=
  match p with
  | InputBit name _ => "input logic " ++ name
  | OutputBit _ name => "output logic " ++ name
  | InputNat name _ => "input int unsigned " ++ name
  | OutputNat _ name => "output int unsigned " ++ name
  end.

Definition portDeclarations := map portDeclaration.

Definition showN (n : N) : string := NilEmpty.string_of_uint (N.to_uint n).

Definition declareBitNets (bc : N) : list string :=
  match bc with
  | N0 => []
  | Npos bc' => ["  logic net[0:" ++ showN (bc - 1) ++ "];"]
  end.

Definition declareNatNets (nc : N) : list string :=
  map (fun i => "  int unsigned nat" ++ showN (N.of_nat i) ++ ";") (seq 0 (N.to_nat nc)).

Definition declareLocalNets (nl : Netlist) : list string :=
  declareBitNets (bitCount nl) ++ declareNatNets (natCount nl).

Definition netS (n : N) : string := "net[" ++ showN n ++ "]".

Definition natS (n : N) : string := "nat" ++ showN n.


Definition instantiateComponent (component : Instance) : string :=
  match component with
  | Inv instNr i o => "  not not_" ++ showN instNr ++ " (" ++
                      netS o ++ ", " ++ netS i ++ ");"
  | And2 instNr i0 i1 o => "  and and_" ++ showN instNr ++ " (" ++ netS o ++ ", " ++  netS i0 ++
                          ", " ++ netS i1 ++ ");"
  | AddMod modVal i0 i1 o => "  assign " ++ natS o ++ " = (" ++ natS i0 ++ " + " ++
                             natS i1 ++ ") % " ++ showN (N.of_nat modVal) ++ ";"
  | NatDelay i o => "  always_ff @(posedge clk) "
                    ++ natS o ++ " <= rst ? 0 : " ++ natS i ++ ";"
  | AssignNat n v => "  assign " ++ natS n ++ " = " ++ natS v  ++ ";"
  | ConstNat n v => "  assign " ++ natS n ++ " = " ++ showN v ++ ";"
  | Comparator a b cf => "  assign " ++ netS cf ++ " = " ++ natS a ++ " == " ++ natS b ++ ";"
  | Mux2 sel a b o => "  assign " ++ natS o ++ " = " ++ netS sel ++ " ? " ++ natS a ++ " : " ++ natS b ++ ";"
  end.

Definition instantiateComponents := map instantiateComponent.
  
Definition declarePorts (pl : list Port) : string :=
  " (input logic clk, input logic rst, " ++ insertCommas (portDeclarations pl) ++ ")".

Definition wireUpPort (p : Port) : string :=
  match p with
  | InputBit name i => "  assign " ++ netS i ++ " = " ++ name ++ ";"
  | OutputBit i name => "  assign " ++ name ++ " = " ++ netS i ++ ";"
  | InputNat name i => "  assign " ++ natS i ++ " = " ++ name ++ ";"
  | OutputNat i name => "  assign " ++ name ++ " = " ++ natS i ++ ";"
  end.

Definition wireUpPorts := map wireUpPort.

Definition systemVerilogLines (nl : Netlist) : list string :=
  ["module " ++ netlistName nl ++ declarePorts (ports nl) ++ ";";
   "timeunit 1ns; timeprecision 1ns;"] ++
  declareLocalNets nl ++
  wireUpPorts (ports nl) ++
  instantiateComponents (instances nl) ++
  ["endmodule"].

Fixpoint unlines (lines : list string) : string :=
  match lines with
  | [] => ""
  | x::xs => x ++ "\n" ++ unlines xs
  end.

Definition systemVerilog (name : string) (nl : state Netlist unit ) : string :=
  unlines (systemVerilogLines (netlist name nl)).

(* A nandGate netlist generation example. *)
Definition nandGate : state Netlist unit :=
  i0 <- inputBit "i0" ;;
  i1 <- inputBit "i1" ;;
  o1 <- and2 (i0, i1) ;;
  o <- inv o1 ;;
  outputBit o "o".

Redirect "nandgate.sv" Compute (systemVerilog "nandGate" nandGate).

Definition addmod : state Netlist unit :=
  a <- inputNat "a" ;;
  b <- inputNat "b" ;;
  c <- addMod 6 (a, b) ;;
  outputNat c "c".

Redirect "addmod.sv" Compute (systemVerilog "addmod" addmod).

Definition delay1 : state Netlist unit :=
  a <- inputNat "a" ;;
  a1 <- natDelay a ;;
  outputNat a1 "a1".

Redirect "delay1.sv" Compute (systemVerilog "delay1" delay1).

Definition pipe2 : state Netlist unit :=
  a <- inputNat "a" ;;
  a1 <- natDelay a ;;
  a2 <- natDelay a1 ;;
  outputNat a2 "a2".

Redirect "pipe2.sv" Compute (systemVerilog "pipe2" pipe2).

Definition counter6 {acorn} {signal} `{Acorn acorn signal} : signal Nat -> acorn (signal Nat) :=
  loop (addMod 6 >=> natDelay >=> fork2).

Definition counter6Top : state Netlist unit :=
  one <- constNat 1 ;;
  count6 <- counter6 one ;;
  outputNat count6 "count6".

Redirect "counter6.sv" Compute (systemVerilog "counter6" counter6Top).  

Definition counter6by4 : state Netlist unit :=
  zero <- constNat 0 ;;
  one <- constNat 1 ;;
  three <- constNat 3 ;;
  count4 <- loop (addMod 4 >=> natDelay >=> fork2) one ;;
  is3 <- comparator (count4, three) ;;
  incVal <- mux2 (is3, (one, zero)) ;;
  count6by4 <- loop (addMod 6 >=> natDelay >=> fork2) incVal ;;
  outputNat count6by4 "count6by4".

Redirect "counter6by4.sv" Compute (systemVerilog "counter6by4" counter6by4). 

(* An example of a nested loop. *)
Definition nestedloop : state Netlist unit :=
  one <- constNat 1 ;;
  o <- loop (snD natDelay >=> addMod 512 >=> loop (addMod 512 >=> natDelay >=> fork2) >=> fork2) one ;;
  outputNat o "o".

Redirect "nestedloop.sv" Compute (systemVerilog "nestedloop" nestedloop).

