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
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Functor.
Require Export ExtLib.Data.List.
Export MonadNotation.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Vectors.Vector.
Import VectorNotations.

Require Import Coq.Lists.List.
Import ListNotations.
Import FunctorNotation.

Require Import Cava.Core.Core.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.Vector.
Require Import Cava.Util.Tuple.

(******************************************************************************)
(* Netlist implementations for the Cava class.                                *)
(******************************************************************************)

Definition invNet (i : Signal Bit) : state CavaState (Signal Bit) :=
  o <- newWire ;;
  addInstance (Not i o) ;;
  ret o.

Definition andNet (i : Signal Bit * Signal Bit) : state CavaState (Signal Bit) :=
  let (i0, i1) := i in
  o <- newWire ;;
  addInstance (And i0 i1 o) ;;
  ret o.

Definition nandNet (i: Signal Bit * Signal Bit) : state CavaState (Signal Bit) :=
  let (i0, i1) := i in
  o <- newWire ;;
  addInstance (Nand i0 i1 o) ;;
  ret o.

Definition orNet (i: Signal Bit * Signal Bit) : state CavaState (Signal Bit) :=
  let (i0, i1) := i in
  o <- newWire ;;
  addInstance (Or i0 i1 o) ;;
  ret o.

Definition norNet (i: Signal Bit * Signal Bit) : state CavaState (Signal Bit) :=
  let (i0, i1) := i in
  o <- newWire ;;
  addInstance (Nor i0 i1 o) ;;
  ret o.

Definition xorNet (i: Signal Bit * Signal Bit) : state CavaState (Signal Bit) :=
  let (i0, i1) := i in
  o <- newWire ;;
  addInstance (Xor i0 i1 o) ;;
  ret o.

Definition xnorNet (i: Signal Bit * Signal Bit) : state CavaState (Signal Bit) :=
  let (i0, i1) := i in
  o <- newWire ;;
  addInstance (Xnor i0 i1 o) ;;
  ret o.

Definition bufNet (i : Signal Bit) : state CavaState (Signal Bit) :=
  o <- newWire ;;
  addInstance (Buf i o) ;;
  ret o.

(******************************************************************************)
(* Xilinx specific FPGA gates                                                 *)
(******************************************************************************)

Local Open Scope N_scope.

Definition lut1Net (f : bool -> bool) (i : Signal Bit) : state CavaState (Signal Bit) :=
  let config := N.b2n (f false) + 2 * N.b2n (f true) in
  o <- newWire ;;
  addInstance (Component "LUT1" [("INIT", HexLiteral 2 config)]
                         [("O", USignal o); ("I0", USignal i)]) ;;
  ret o.

Definition lut2Net (f : bool -> bool -> bool) (i : Signal Bit * Signal Bit) :
           state CavaState (Signal Bit) :=
  let config :=     N.b2n (f false false) +
                2 * N.b2n (f true false) +
                4 * N.b2n (f false true) +
                8 * N.b2n (f true true) in
  let (i0, i1) := i in
  o <- newWire ;;
  addInstance (Component "LUT2" [("INIT", HexLiteral 4 config)]
                         [("O", USignal  o); ("I0", USignal i0); ("I1", USignal i1)]) ;;
  ret o.

Definition f3List (f: bool -> bool -> bool -> bool) (l: list bool) : bool :=
  match l with
  | [a; b; c] => f a b c
  | _ => false
  end.

Definition lut3Net (f : bool -> bool -> bool -> bool)
                   (i : Signal Bit * Signal Bit * Signal Bit) : state CavaState (Signal Bit) :=
  let powers := map (fun p => let bv := N.to_list_bits_sized 3 (N.of_nat p) in
                     2^(N.of_nat p) * N.b2n (f3List f bv)) (List.seq 0 8)  in
  let config := fold_left N.add powers 0 in
  let '(i0, i1, i2) := i in
  o <- newWire ;;
  addInstance (Component "LUT3" [("INIT", HexLiteral 8 config)]
                         [("O", USignal o); ("I0", USignal i0); ("I1", USignal i1); ("I2", USignal i2)]) ;;
  ret o.

Definition f4List (f: bool -> bool -> bool -> bool -> bool) (l: list bool) :
  bool :=
  match l with
  | [a; b; c; d] => f a b c d
  | _ => false
  end.

Definition lut4Net (f : bool -> bool -> bool -> bool -> bool)
                   (i : Signal Bit * Signal Bit * Signal Bit * Signal Bit) :
                  state CavaState (Signal Bit) :=
  let powers := map (fun p => let bv := N.to_list_bits_sized 4 (N.of_nat p) in
                     2^(N.of_nat p) * N.b2n (f4List f bv)) (seq 0 16)  in
  let config := fold_left N.add powers 0 in
  let '(i0, i1, i2, i3) := i in
  o <- newWire ;;
  addInstance (Component "LUT4" [("INIT", HexLiteral 16 config)]
                          [("O", USignal  o); ("I0", USignal i0); ("I1", USignal  i1); ("I2", USignal i2); ("I3", USignal i3)]) ;;
  ret o.

Definition f5List (f: bool -> bool -> bool -> bool -> bool -> bool)
                  (l: list bool) : bool :=
  match l with
  | [a; b; c; d; e] => f a b c d e
  | _ => false
  end.

Definition lut5Net (f : bool -> bool -> bool -> bool -> bool -> bool)
                  (i : Signal Bit * Signal Bit * Signal Bit * Signal Bit * Signal Bit) : state CavaState (Signal Bit) :=
  let powers := map (fun p => let bv := N.to_list_bits_sized 5 (N.of_nat p) in
                     2^(N.of_nat p) * N.b2n (f5List f bv)) (seq 0 32)  in
  let config := fold_left N.add powers 0 in
  let '(i0, i1, i2, i3, i4) := i in
  o <- newWire ;;
  addInstance (Component "LUT5" [("INIT", HexLiteral 32 config)]
                          [("O", USignal o); ("I0", USignal i0); ("I1", USignal i1); ("I2", USignal i2); ("I3", USignal i3); ("I4", USignal i4)]) ;;
  ret o.

Definition f6List (fn: bool -> bool -> bool -> bool -> bool -> bool -> bool)
                  (l: list bool) : bool :=
  match l with
  | [a; b; c; d; e; f] => fn a b c d e f
  | _ => false
  end.

Definition lut6Net (f : bool -> bool -> bool -> bool -> bool -> bool -> bool)
                  (i : Signal Bit * Signal Bit * Signal Bit * Signal Bit * Signal Bit * Signal Bit) : state CavaState (Signal Bit) :=
  let powers := map (fun p => let bv := N.to_list_bits_sized 6 (N.of_nat p) in
                     2^(N.of_nat p) * N.b2n (f6List f bv)) (seq 0 64)  in
  let config := fold_left N.add powers 0 in
  let '(i0, i1, i2, i3, i4, i5) := i in
  o <- newWire ;;
  addInstance (Component "LUT6" [("INIT", HexLiteral 64 config)]
                          [("O", USignal o); ("I0", USignal i0); ("I1", USignal i1); ("I2", USignal i2); ("I3", USignal i3); ("I4", USignal i4); ("I5", USignal i5)] ) ;;
  ret o.

Local Close Scope N_scope.

Definition xorcyNet (i : Signal Bit * Signal Bit) : state CavaState (Signal Bit) :=
  let (ci, li) := i in
  o <- newWire ;;
  addInstance (Component "XORCY" [] [("O", USignal o); ("CI", USignal (fst i)); ("LI", USignal (snd i))]) ;;
  ret o.

Definition muxcyNet (s ci di : Signal Bit) : state CavaState (Signal Bit) :=
  o <- newWire ;;
  addInstance (Component "MUXCY" [] [("O", USignal o); ("S", USignal s); ("CI", USignal ci); ("DI", USignal di)]) ;;
  ret o.

Definition localSignalNet {A : SignalType}
                          (v : Signal A)
                          : state CavaState (Signal A) :=
   localSig <- newSignal A ;;
   assignSignal localSig v ;;
   ret localSig.

Definition unpackVNet {t : SignalType} {s : nat} (v : Signal (Vec t s))
  : state CavaState (Vector.t (Signal t) s) :=
  mapT_vector (fun x => localSignalNet (IndexConst v x)) (vseq 0 s).

Definition packVNet {t : SignalType} {s : nat} (v: Vector.t (Signal t) s)
  : state CavaState (Signal (Vec t s)) :=
  localSignalNet (VecLit v).

Fixpoint combToSignal (t : SignalType) (v : combType t) : Signal t :=
  match t, v with
  | Void, _ => UndefinedSignal
  | Bit, bv => match bv with
               | false => Gnd
               | true => Vcc
               end
  | Vec vt s, v => VecLit (Vector.map (combToSignal vt) v)
  | ExternalType typ, _ => UninterpretedSignal typ
  end.

(******************************************************************************)
(* Instantiate the Cava class for CavaNet which describes circuits without    *)
(* any top-level pins or other module-level data                              *)
(******************************************************************************)

Instance CavaCombinationalNet : Cava denoteSignal := {
    cava := state CavaState;
    monad := Monad_state _;
    constant b := if b then Vcc else Gnd;
    constantV A n v := VecLit v;
    defaultSignal := defaultNetSignal;
    inv := invNet;
    and2 := andNet;
    nand2 := nandNet;
    or2 := orNet;
    nor2 := norNet;
    xor2 := xorNet;
    xnor2 := xnorNet;
    buf_gate := bufNet;
    lut1 := lut1Net;
    lut2 := lut2Net;
    lut3 := lut3Net;
    lut4 := lut4Net;
    lut5 := lut5Net;
    lut6 := lut6Net;
    xorcy := xorcyNet;
    muxcy := muxcyNet;
    unpackV := @unpackVNet;
    packV := @packVNet;
    indexAt k sz isz v i := localSignalNet (IndexAt v i);
    unsignedAdd m n ab :=
      localSignalNet (@UnsignedAdd m n (1 + max m n) (fst ab) (snd ab));
    unsignedMult m n ab :=
      localSignalNet (@UnsignedMultiply m n (m + n) (fst ab) (snd ab));
    greaterThanOrEqual m n ab :=
      localSignalNet (@GreaterThanOrEqual m n (fst ab) (snd ab));
    localSignal := @localSignalNet;
    instantiate intf circuit a :=
      let cs := makeNetlist intf circuit in
      addModule intf (module cs) ;;
      blackBoxNet intf a;
    blackBox := blackBoxNet;
}.

(* Run circuit for a single step *)
Fixpoint interpCircuit {i o} (c : Circuit i o)
    : value i -> state CavaState (value o) :=
  match c in Circuit i o return value i -> state CavaState (value o) with
  | Comb f => f
  | Compose f g =>
    fun input =>
      x <- interpCircuit f input ;;
      y <- interpCircuit g x ;;
      ret y
  | Par f g =>
    fun input =>
      x <- interpCircuit f (fst input) ;;
      y <- interpCircuit g (snd input) ;;
      ret (x, y)
  | @LoopInitCE _ _ i o s resetval f =>
    fun '(input, en) =>
      feedback_in <- newSignals s ;;
      '(out, feedback_out) <- interpCircuit f (input, feedback_in) ;;
      (* place a delay on each of the feedback wires *)
      addDelays resetval en feedback_out feedback_in ;;
      ret out
  | @DelayInit _ _ t resetval =>
    fun input =>
      out <- newSignals t ;;
      addDelays resetval Vcc input out ;;
      ret out
  end.


Definition makeCircuitNetlist (intf : CircuitInterface)
           (c : Circuit (circuitInputs intf) (circuitOutputs intf)) : CavaState :=
  makeNetlist intf (interpCircuit c).

