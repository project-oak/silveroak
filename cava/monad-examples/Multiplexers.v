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

From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.

From Coq Require Import Lists.List.
Import ListNotations.

Require Import Omega.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Cava.
Require Import Cava.Monad.CavaMonad.

From Coq Require Vector.
From Coq Require Import Bool.Bvector.
Import Vector.VectorNotations.

From Coq Require Import NArith.Ndigits.

Local Open Scope vector_scope.

Definition mux2_1 {m bit} `{Cava m bit} (sab: bit * (bit * bit)) : m bit :=
  let '(sel, (a, b)) := sab in
  ret (indexBitAt ([a; b]) [sel]).

Local Close Scope vector_scope.

Example m1: combinational (mux2_1 (false, (false, true))) = false.
Proof. reflexivity. Qed.

Example m2: combinational (mux2_1 (false, (true, false))) = true.
Proof. reflexivity. Qed.

Example m3: combinational (mux2_1 (true, (false, true))) = true.
Proof. reflexivity. Qed.

Example m4: combinational (mux2_1 (true, (true, false))) = false.
Proof. reflexivity. Qed.

Definition mux2_1_Interface
  := combinationalInterface "mux2_1"
     (mkPort "sel" Bit, (mkPort "i0" Bit, mkPort "i1" Bit))
     (mkPort "o" Bit)
     [].

Definition mux2_1Netlist := makeNetlist mux2_1_Interface mux2_1.

Definition mux2_1_tb_inputs :=
  [(false, (false, true));
   (false, (true, false));
   (true, (false, true));
    (true, (true, false))].

Definition mux2_1_tb_expected_outputs
  := map (fun i => combinational (mux2_1 i)) mux2_1_tb_inputs.

Definition mux2_1_tb
  := testBench "mux2_1_tb" mux2_1_Interface
     mux2_1_tb_inputs mux2_1_tb_expected_outputs.

 Section index_at_test.

  (* Check the indexBitAt special case *)

  Definition mux2_1_bit {m bit} `{Cava m bit} {sz isz: nat}
                        (vsel: Vector.t bit sz * Vector.t bit isz) : m bit :=
  let (v, sel) := vsel in
  ret (indexBitAt v sel).

   Definition v := N2Bv_sized 4  11.
   (*
   Bit pattern for 11:
   -- 3 2 1 0 (bit position)
   -- 8 4 2 1 (power)
   -- 1 0 1 1 (bit pattern for 11)
   *)

   Definition i0 := N2Bv_sized 2 0.
   Definition i1 := N2Bv_sized 2 1.
   Definition i2 := N2Bv_sized 2 2.
   Definition i3 := N2Bv_sized 2 3.

   Example index_bit_0 : combinational (mux2_1_bit (v, i0)) = true.
   Proof. reflexivity. Qed.

   Example index_bit_1 : combinational (mux2_1_bit (v, i1)) = true.
   Proof. reflexivity. Qed.

   Example index_bit_2 : combinational (mux2_1_bit (v, i2)) = false.
   Proof. reflexivity. Qed.

   Example index_bit_3 : combinational (mux2_1_bit (v, i3)) = true.
   Proof. reflexivity. Qed.

  Definition mux2_1_bit_Interface
    := combinationalInterface "mux2_1_bit"
       (mkPort "v" (BitVec Bit 4),
        mkPort "sel" (BitVec Bit 2))
       (mkPort "o" Bit)
       [].

  Definition mux2_1_bit_Netlist := makeNetlist mux2_1_bit_Interface mux2_1_bit.

  Definition mux2_1_bit_tb_inputs :=
    [(v, i0);
     (v, i1);
     (v, i2);
     (v, i3)].

  Definition mux2_1_bit_tb_expected_outputs
  := map (fun i => combinational (mux2_1_bit i)) mux2_1_bit_tb_inputs.

 Definition mux2_1_bit_tb
  := testBench "mux2_1_bit_tb" mux2_1_bit_Interface
     mux2_1_bit_tb_inputs mux2_1_bit_tb_expected_outputs.

 End index_at_test.

(* Mux between input buses *)

Definition muxBusAlt {m bit} `{Cava m bit} {k} {sz isz: nat}
                     (vsel: smashTy bit (BitVec k sz) *
                            Vector.t bit isz) :
                     m (smashTy bit k) :=
  let (v, sel) := vsel in
  ret (indexAt v sel).

Definition muxBus {m bit} `{Cava m bit} {sz isz dsz: nat}
                     (vsel: Vector.t (smashTy bit (BitVec Bit dsz)) sz *
                            Vector.t bit isz) :
                     m (smashTy bit (BitVec Bit dsz)) :=
  let (v, sel) := vsel in
  ret (indexAt v sel).

Definition muxBus4_8 {m bit} `{Cava m bit}
                     (vsel: Vector.t (smashTy bit (BitVec Bit 8)) 4 *
                            Vector.t bit 2) :
                     m (smashTy bit (BitVec Bit 8)) :=
  let (v, sel) := vsel in
  ret (indexAt v sel).

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
     (mkPort "i" (BitVec (BitVec Bit 8) 4), mkPort "sel" (BitVec Bit 2))
     (mkPort "o" (BitVec Bit 8))
     [].

Definition muxBus4_8Netlist := makeNetlist muxBus4_8Interface muxBus4_8.

Definition muxBus4_8_tb_inputs :=
  [(v0to3, [false; false]%vector);
   (v0to3, [true;  false]%vector);
   (v0to3, [false; true]%vector);
   (v0to3, [true; true]%vector)
  ].

Definition muxBus4_8_tb_expected_outputs
  := map (fun i => combinational (muxBus i)) muxBus4_8_tb_inputs.

Definition muxBus4_8_tb
  := testBench "muxBus4_8_tb" muxBus4_8Interface
     muxBus4_8_tb_inputs muxBus4_8_tb_expected_outputs.
