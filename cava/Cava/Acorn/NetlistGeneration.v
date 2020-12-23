(****************************************************************************)
(* Copyright 2020 The Project Oak Authors                                   *)
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
Export MonadNotation.

Require Import Coq.ZArith.ZArith.

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Cava.Cava.
Require Import Cava.Acorn.CavaClass.

Require Import Cava.Signal.

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
  let powers := map (fun p => let bv := nat_to_list_bits_sized 3 (N.of_nat p) in
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
  let powers := map (fun p => let bv := nat_to_list_bits_sized 4 (N.of_nat p) in
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
  let powers := map (fun p => let bv := nat_to_list_bits_sized 5 (N.of_nat p) in
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
  let powers := map (fun p => let bv := nat_to_list_bits_sized 6 (N.of_nat p) in
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

Definition unpairNet {t1 t2 : SignalType} (v : Signal (Pair t1 t2)) : Signal t1 * Signal t2 :=
  (SignalFst v, SignalSnd v).

Definition mkpairNet {t1 t2 : SignalType} (v1 : Signal t1) (v2 : Signal t2) : Signal (Pair t1 t2) :=
  SignalPair v1 v2.

Definition peelNet {t : SignalType} {s : nat} (v : Signal (Vec t s)) : Vector.t (Signal t) s :=
  Vector.map (IndexConst v) (vseq 0 s).

Definition unpeelNet {t : SignalType} {s : nat} (v: Vector.t (Signal t) s) : Signal (Vec t s) :=
  VecLit v.

Definition sliceNet {t: SignalType} {sz: nat}
                    (startAt len: nat)
                    (v: Signal (Vec t sz))
                    (H: startAt + len <= sz) :
                    Signal (Vec t len) :=
  unpeelNet (sliceVector (peelNet v) startAt len H).

Definition unsignedAddNet {m n : nat}
                          (a : Signal (Vec Bit m))
                          (b : Signal (Vec Bit n)) :
                          state CavaState (Signal (Vec Bit (1 + max m n))) :=
  sum <- newVector Bit (1 + max m n) ;;
  addInstance (UnsignedAdd a b sum) ;;
  ret sum.

Definition unsignedMultNet {m n : nat}
                           (a : Signal (Vec Bit m))
                           (b : Signal (Vec Bit n)) :
                           state CavaState (Signal (Vec Bit (m + n))) :=
  product <- newVector Bit (m + n) ;;
  addInstance (UnsignedMultiply a b product) ;;
  ret product.

Definition greaterThanOrEqualNet {m n : nat}
                                 (a : Signal (Vec Bit m)) (b : Signal (Vec Bit n)) :
                                 state CavaState (Signal Bit) :=
  comparison <- newWire ;;
  addInstance (GreaterThanOrEqual a b comparison) ;;
  ret comparison.

Definition delayNet (t: SignalType)
                    (i : Signal t)
                    : state CavaState (Signal t) :=
  o <- newSignal t ;;
  addInstance (Delay t i o) ;;
  ret o.

Definition delayEnableNet (t : SignalType)
                          (en : Signal Bit)
                          (i : Signal t)
                          : state CavaState (Signal t) :=
  o <- newSignal t ;;
  addInstance (DelayEnable t en i o) ;;
  ret o.

Local Open Scope type_scope.

(* Create a loop circuit with a delay element along the feedback path. *)
Definition loopNet (A B C : SignalType)
                   (f : Signal A * Signal C -> state CavaState (Signal B * Signal C))
                   (a : Signal A)
                   : state CavaState (Signal B) :=
  o <- @newSignal C ;;
  '(b, cOut) <- f (a, o) ;;
  oDelay <- delayNet C cOut ;;
  assignSignal o oDelay ;;
  ret b.

(* Create a loop circuit with a delay element with enable along the feedback path. *)
Definition loopNetEnable (A B C : SignalType)
                         (en : Signal Bit)
                         (f : Signal A * Signal C -> state CavaState (Signal B * Signal C))
                         (a : Signal A)
                         : state CavaState (Signal B) :=
  o <- @newSignal C ;;
  '(b, cOut) <- f (a, o) ;;
  oDelay <- delayEnableNet C en cOut ;;
  assignSignal o oDelay ;;
  ret b.

Definition instantiateNet (intf : CircuitInterface)
                          (circuit : tupleNetInterface (circuitInputs intf) ->
                                    state CavaState (tupleNetInterface (circuitOutputs intf)))
                          (a : tupleNetInterface (circuitInputs intf))
                          : state CavaState (tupleNetInterface (circuitOutputs intf)) :=
  let cs := makeNetlist intf circuit in
  addModule intf (module cs) ;;
  x <- blackBoxNet intf a ;;
  ret x.

(******************************************************************************)
(* Instantiate the Cava class for CavaNet which describes circuits without    *)
(* any top-level pins or other module-level data                              *)
(******************************************************************************)

Instance CavaCombinationalNet : Cava denoteSignal := {
    cava := state CavaState;
    zero := ret Gnd;
    one := ret Vcc;
    defaultSignal := defaultNetSignal;
    inv := invNet;
    and2 := andNet;
    nand2 := nandNet;
    or2 := orNet;
    nor2 := norNet;
    xor2 := xorNet;
    xnor2 := xorNet;
    buf_gate := bufNet;
    lut1 := lut1Net;
    lut2 := lut2Net;
    lut3 := lut3Net;
    lut4 := lut4Net;
    lut5 := lut5Net;
    lut6 := lut6Net;
    xorcy := xorcyNet;
    muxcy := muxcyNet;
    mkpair := @mkpairNet;
    unpair := @unpairNet;
    peel := @peelNet;
    unpeel := @unpeelNet;
    pairSel := @SignalSel;
    indexAt k sz isz := IndexAt;
    indexConst k sz := IndexConst;
    slice k sz := @sliceNet k sz;
    unsignedAdd m n := @unsignedAddNet m n;
    unsignedMult m n := @unsignedMultNet m n;
    greaterThanOrEqual m n := @greaterThanOrEqualNet m n;
    instantiate := instantiateNet;
    blackBox := blackBoxNet;
}.

Instance CavaSequentialNet : CavaSeq CavaCombinationalNet :=
  { delay k := delayNet k;
    delayEnable k := delayEnableNet k;
    loopDelay a b c := loopNet a b c;
    loopDelayEnable en a b c := loopNetEnable en a b c;
  }.
