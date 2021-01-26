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

Require Import Coq.Bool.Bool Coq.NArith.NArith.
Require Import Coq.Strings.Ascii Coq.Strings.String.

Require Import Coq.Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.

Require Import Coq.Bool.Bvector.
Import Vector.VectorNotations.

Local Open Scope vector_scope.

Section WithCava.
  Context {signal} `{Cava signal} `{Monad cava}.

  (* muxPair specialized to single bit inputs *)
  Definition mux2_1: signal Bit -> signal Bit * signal Bit -> cava (signal Bit)
  := muxPair.

  Definition mux2_1_top '(sel, a, b) := mux2_1 sel (a, b).

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
(* muxPair tests                                                              *)
(******************************************************************************)

Definition mux2_1_tb_inputs :=
  [(false, false, true);
   (false, true,  false);
   (true,  false, true);
   (true,  true,  false)].

(* Transpose test vectors for use in Coq simulation. *)
(* Satnam asks: why can't [Bit; Bit; Bit] be inferred? *)
Definition mux2_1_tb_inputs' := fromListOfTuples [Bit; Bit; Bit] mux2_1_tb_inputs.

(* Enumerate the expected outputs. *)
Definition muxManualExpectedOutputs := [false; true; true; false].

Definition mux2_1_tb_expected_outputs := combinational (mux2_1_top mux2_1_tb_inputs').

Example m1_4: mux2_1_tb_expected_outputs = muxManualExpectedOutputs.
Proof. reflexivity. Qed.

Definition mux2_1_Interface
  := combinationalInterface "mux2_1"
     [mkPort "sel" Bit; mkPort "i0" Bit; mkPort "i1" Bit]
     [mkPort "o" Bit]
     [].

Definition mux2_1Netlist
  := makeNetlist mux2_1_Interface (fun '(sel, a, b) => mux2_1 sel (a, b)).

(* The test bench ensures the generated SystemVerilog for this mux2 circuit
   has the same behaviour as the Coq simulation semantics. *)
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

Example m5: combinational (muxBus ([v0to3]%list, [[false; false]%vector]%list)) = [v0]%list.
Proof. reflexivity. Qed.

Example m6: combinational (muxBus ([v0to3]%list, [[true; false]%vector]%list)) = [v1]%list.
Proof. reflexivity. Qed.

Example m7: combinational (muxBus ([v0to3]%list, [[false; true]%vector]%list)) = [v2]%list.
Proof. reflexivity. Qed.

Example m8: combinational (muxBus ([v0to3]%list, [[true; true]%vector]%list)) = [v3]%list.
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
  := map (fun '(i0,i1) => List.hd (defaultCombValue _)
                               (combinational (muxBus ([i0],[i1])%list)))
         muxBus4_8_tb_inputs.

Definition muxBus4_8_tb
  := testBench "muxBus4_8_tb" muxBus4_8Interface
     muxBus4_8_tb_inputs muxBus4_8_tb_expected_outputs.
