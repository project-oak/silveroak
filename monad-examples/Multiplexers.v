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

From Coq Require Import Bool.Bool NArith.NArith.
From Coq Require Import Strings.Ascii Strings.String.

From Coq Require Import Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Cava.
Require Import Cava.Monad.CavaMonad.

From Coq Require Vectors.Vector.
From Coq Require Import Bool.Bvector.
Import Vector.VectorNotations.

From Coq Require Import NArith.Ndigits.

Local Open Scope vector_scope.

Section WithCava.
  Context {signal} `{Cava signal} `{Monad cava}.

Definition mux2_1 (sab: signal Bit * signal Bit * signal Bit) : cava (signal Bit) :=
  let '(sel, a, b) := sab in
  ret (indexAt (unpeel [a; b]) (unpeel [sel])).

  (* Mux between input buses *)

  Definition muxBus {dsz sz isz: nat}
                     (vsel: signal (Vec (Vec Bit dsz) sz) *
                           signal (Vec Bit isz)) :
                      cava (signal (Vec Bit dsz)) :=
    let (v, sel) := vsel in
    ret (indexAt v sel).

End WithCava.

Local Close Scope vector_scope.

(******************************************************************************)
(* mux2_1                                                                     *)
(******************************************************************************)

Example m1: combinational (mux2_1 (false, false, true)) = false.
Proof. reflexivity. Qed.

Example m2: combinational (mux2_1 (false, true, false)) = true.
Proof. reflexivity. Qed.

Example m3: combinational (mux2_1 (true, false, true)) = true.
Proof. reflexivity. Qed.

Example m4: combinational (mux2_1 (true, true, false)) = false.
Proof. reflexivity. Qed.

Definition mux2_1_Interface
  := combinationalInterface "mux2_1"
     [mkPort "sel" Bit; mkPort "i0" Bit; mkPort "i1" Bit]
     [mkPort "o" Bit]
     [].

Definition mux2_1Netlist := makeNetlist mux2_1_Interface mux2_1.

Definition mux2_1_tb_inputs :=
  [(false, false, true);
   (false, true,  false);
   (true,  false, true);
   (true,  true,  false)].

Definition mux2_1_tb_expected_outputs
  := map (fun i => combinational (mux2_1 i)) mux2_1_tb_inputs.

Definition mux2_1_tb
  := testBench "mux2_1_tb" mux2_1_Interface
     mux2_1_tb_inputs mux2_1_tb_expected_outputs.

(******************************************************************************)
(* muxBus                                                                     *)
(******************************************************************************)

Local Open Scope vector_scope.
Definition v0 := N2Bv_sized 8   5.
Definition v1 := N2Bv_sized 8 157.
Definition v2 := N2Bv_sized 8 255.
Definition v3 := N2Bv_sized 8  63.
Definition v0to3 : Vector.t (Bvector 8) 4 := [v0; v1; v2; v3].

Example m5: combinational (muxBus (v0to3, [false; false])) = v0.
Proof. reflexivity. Qed.

Example m6: combinational (muxBus (v0to3, [true; false])) = v1.
Proof. reflexivity. Qed.

Example m7: combinational (muxBus (v0to3, [false; true])) = v2.
Proof. reflexivity. Qed.

Example m8: combinational (muxBus (v0to3, [true; true])) = v3.
Proof. reflexivity. Qed.

Local Close Scope vector_scope.

Definition muxBus4_8Interface
  := combinationalInterface "muxBus4_8"
     [mkPort "i" (Vec (Vec Bit 8) 4); mkPort "sel" (Vec Bit 2)]
     [mkPort "o" (Vec Bit 8)]
     [].

Definition muxBus4_8Netlist := makeNetlist muxBus4_8Interface muxBus.

Definition muxBus4_8_tb_inputs : list (Vector.t (Bvector 8) 4 * Vector.t bool 2) :=
  [(v0to3, [false; false]%vector);
   (v0to3, [true;  false]%vector);
   (v0to3, [false; true]%vector);
   (v0to3, [true; true]%vector)
  ].

Definition muxBus4_8_tb_expected_outputs : list (Bvector 8)
  := map (fun i => combinational (muxBus i)) muxBus4_8_tb_inputs.

Definition muxBus4_8_tb
  := testBench "muxBus4_8_tb" muxBus4_8Interface
     muxBus4_8_tb_inputs muxBus4_8_tb_expected_outputs.
