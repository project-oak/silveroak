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

From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import ExtLib.Structures.Monads.
Export MonadNotation.

From Coq Require Import ZArith.

Require Import Cava.Cava.
Require Import Cava.Monad.CavaClass.

Require Import Cava.Signal.

(******************************************************************************)
(* Netlist implementations for the Cava class.                                *)
(******************************************************************************)

Definition invNet (i : Signal) : state CavaState Signal :=
  o <- newWire ;;
  addInstance (Not i o) ;;
  ret o.

Definition andNet (i : Signal * Signal) : state CavaState Signal :=
  let (i0, i1) := i in
  o <- newWire ;;
  addInstance (And i0 i1 o) ;;
  ret o.

Definition nandNet (i : Signal * Signal) : state CavaState Signal :=
  let (i0, i1) := i in
  o <- newWire ;;
  addInstance (Nand i0 i1 o) ;;
  ret o.

Definition orNet (i : Signal * Signal) : state CavaState Signal :=
  let (i0, i1) := i in
  o <- newWire ;;
  addInstance (Or i0 i1 o) ;;
  ret o.

Definition norNet (i : Signal * Signal) : state CavaState Signal :=
  let (i0, i1) := i in
  o <- newWire ;;
  addInstance (Nor i0 i1 o) ;;
  ret o.

Definition xorNet (i : Signal * Signal) : state CavaState Signal :=
  let (i0, i1) := i in
  o <- newWire ;;
  addInstance (Xor i0 i1 o) ;;
  ret o.

Definition xnorNet (i : Signal * Signal) : state CavaState Signal :=
  let (i0, i1) := i in
  o <- newWire ;;
  addInstance (Xnor i0 i1 o) ;;
  ret o.

Definition bufNet (i : Signal) : state CavaState Signal :=
  o <- newWire ;;
  addInstance (Buf i o) ;;
  ret o.

(******************************************************************************)
(* Xilinx specific FPGA gates                                                 *)
(******************************************************************************)

Local Open Scope N_scope.

Definition lut1Net (f : bool -> bool) (i : Signal) : state CavaState Signal :=
  let config := N.b2n (f false) + 2 * N.b2n (f true) in
  o <- newWire ;;
  addInstance (Component "LUT1" [("INIT", HexLiteral 2 config)]
                         [("O", o); ("I0", i)]) ;;
  ret o.

Definition lut2Net (f : bool -> bool -> bool) (i : Signal * Signal) :
           state CavaState Signal :=
  let config :=     N.b2n (f false false) +
                2 * N.b2n (f true false) +
                4 * N.b2n (f false true) + 
                8 * N.b2n (f true true) in
  let (i0, i1) := i in
  o <- newWire ;;
  addInstance (Component "LUT2" [("INIT", HexLiteral 4 config)]
                         [("O", o); ("I0", i0); ("I1", i1)]) ;;
  ret o.                       

Definition f3List (f: bool -> bool -> bool -> bool) (l: list bool) : bool :=
  match l with
  | [a; b; c] => f a b c
  | _ => false
  end.

Definition lut3Net (f : bool -> bool -> bool -> bool)
                   (i : Signal * Signal * Signal) : state CavaState Signal :=
  let powers := map (fun p => let bv := nat_to_list_bits_sized 3 (N.of_nat p) in
                     2^(N.of_nat p) * N.b2n (f3List f bv)) (seq 0 8)  in
  let config := fold_left N.add powers 0 in
  let '(i0, i1, i2) := i in
  o <- newWire ;;
  addInstance (Component "LUT3" [("INIT", HexLiteral 8 config)]
                         [("O", o); ("I0", i0); ("I1", i1); ("I2", i2)]) ;;
  ret o.

Definition f4List (f: bool -> bool -> bool -> bool -> bool) (l: list bool) :
  bool :=
  match l with
  | [a; b; c; d] => f a b c d
  | _ => false
  end.

Definition lut4Net (f : bool -> bool -> bool -> bool -> bool)
                   (i : Signal * Signal * Signal * Signal) :
                  state CavaState Signal :=
  let powers := map (fun p => let bv := nat_to_list_bits_sized 4 (N.of_nat p) in
                     2^(N.of_nat p) * N.b2n (f4List f bv)) (seq 0 16)  in
  let config := fold_left N.add powers 0 in
  let '(i0, i1, i2, i3) := i in
  o <- newWire ;;
  addInstance (Component "LUT4" [("INIT", HexLiteral 16 config)]
                          [("O", o); ("I0", i0); ("I1", i1); ("I2", i2); ("I3", i3)]) ;;
  ret o.

Definition f5List (f: bool -> bool -> bool -> bool -> bool -> bool)
                  (l: list bool) : bool :=
  match l with
  | [a; b; c; d; e] => f a b c d e
  | _ => false
  end.

Definition lut5Net (f : bool -> bool -> bool -> bool -> bool -> bool)
                  (i : Signal * Signal * Signal * Signal * Signal) : state CavaState Signal :=
  let powers := map (fun p => let bv := nat_to_list_bits_sized 5 (N.of_nat p) in
                     2^(N.of_nat p) * N.b2n (f5List f bv)) (seq 0 32)  in
  let config := fold_left N.add powers 0 in
  let '(i0, i1, i2, i3, i4) := i in
  o <- newWire ;;
  addInstance (Component "LUT5" [("INIT", HexLiteral 32 config)]
                          [("O", o); ("I0", i0); ("I1", i1); ("I2", i2); ("I3", i3); ("I4", i4)]) ;;
  ret o.                        

Definition f6List (fn: bool -> bool -> bool -> bool -> bool -> bool -> bool)
                  (l: list bool) : bool :=
  match l with
  | [a; b; c; d; e; f] => fn a b c d e f
  | _ => false
  end.

Definition lut6Net (f : bool -> bool -> bool -> bool -> bool -> bool -> bool)
                  (i : Signal * Signal * Signal * Signal * Signal * Signal) : state CavaState Signal :=
  let powers := map (fun p => let bv := nat_to_list_bits_sized 6 (N.of_nat p) in
                     2^(N.of_nat p) * N.b2n (f6List f bv)) (seq 0 64)  in
  let config := fold_left N.add powers 0 in
  let '(i0, i1, i2, i3, i4, i5) := i in 
  o <- newWire ;;
  addInstance (Component "LUT6" [("INIT", HexLiteral 64 config)]
                          [("O", o); ("I0", i0); ("I1", i1); ("I2", i2); ("I3", i3); ("I4", i4); ("I5", i5)] ) ;;
  ret o.

Local Close Scope N_scope.

Definition xorcyNet (i : Signal * Signal) : state CavaState Signal :=
  let (ci, li) := i in
  o <- newWire ;;
  addInstance (Component "XORCY" [] [("O", o); ("CI", fst i); ("LI", snd i)]) ;;
  ret o.

Definition muxcyNet (s ci di : Signal) : state CavaState Signal :=
  o <- newWire ;;
  addInstance ( Component "MUXCY" [] [("O", o); ("S", s); ("CI", ci); ("DI", di)]) ;;
  ret o.

Definition indexBitArrayNet (i : list Signal) (sel : list Signal) :
                            state CavaState Signal :=
  o <- newWire ;;
  addInstance (IndexBitArray i sel o) ;;
  ret o.

Definition indexArrayNet (i : list (list Signal)) (sel : list Signal) :
                         state CavaState (list Signal) :=
  let w := length (hd [] i) in (* The width of each bus *)
  let m := length sel in       (* Number of bits to represent selector *)
  let n := length i in         (* Number of values to select from *)
  o <- newWires w ;;
  addInstance (IndexArray i sel o) ;;
  ret o.

Definition unsignedAddNet (a : list Signal) (b : list Signal) :
                          state CavaState (list Signal) :=
  let sumSize := max (length a) (length b) + 1 in
  sum <- newWires sumSize ;;
  addInstance (UnsignedAdd a b sum) ;;
  ret sum.

Definition delayBitNet (i : Signal) : state CavaState Signal :=
  o <- newWire ;;
  addSequentialInstance (DelayBit i o) ;;
  ret o.

Definition loopBitNet (A B : Type) (f : (A * Signal)%type -> state CavaState (B * Signal)%type) (a : A) : state CavaState B :=
  o <- newWire ;;
  '(b, cOut) <- f (a, o) ;;
  addInstance (AssignBit o cOut) ;;
  ret b.

(******************************************************************************)
(* Instantiate the Cava class for CavaNet which describes circuits without    *)
(* any top-level pins or other module-level data                              *)
(******************************************************************************)

Instance CavaNet : Cava (state CavaState) Signal :=
  { zero := ret Gnd;
    one := ret Vcc;
    delayBit := delayBitNet;
    loopBit a b := loopBitNet a b;
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
    indexBitArray := indexBitArrayNet;
    indexArray := indexArrayNet;
    unsignedAdd := unsignedAddNet;
}.
