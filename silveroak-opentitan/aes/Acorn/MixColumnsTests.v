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

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Vectors.Vector.
Import VectorNotations.

Require Import Coq.NArith.Ndigits.
Require Import Coq.NArith.BinNat.

Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.

Require Import AesSpec.StateTypeConversions.
Require Import AcornAes.MixColumnsCircuit.
Require Import AesSpec.Tests.CipherTest.
Require Import AesSpec.Tests.Common.
Require Import AesSpec.AES256.

Local Open Scope vector_scope.

Definition mixColTest1ExpectedOutput : Vector.t (Vector.t nat 4) 4
  := [[142; 77; 161; 188];
      [159; 220; 88; 157];
      [1; 1; 1; 1];
      [77; 126; 189; 248]].

(*** First work with MixCols.mix_cols spec. ***)

(* A function to convert a matrix of nat values to a valyue of type state *)
Definition fromNatState (i : Vector.t (Vector.t nat 4) 4 ): Vector.t (Vector.t Byte.byte 4) 4
  := Vector.map (Vector.map (fun v => bitvec_to_byte (N2Bv_sized 8 (N.of_nat v)))) i.

(* A function to convert a state value to a matrix of nat values. *)
Definition toNatState (i: Vector.t (Vector.t Byte.byte 4) 4) : Vector.t (Vector.t nat 4) 4
  := Vector.map (Vector.map (fun v => N.to_nat (Bv2N (byte_to_bitvec v)))) i.

Definition mixColTestInputs' : Vector.t (Vector.t Byte.byte 4) 4 := fromNatState mixColTest1InputNat.

Definition s1 : Vector.t (Vector.t Byte.byte 4) 4 := MixColumns.mix_columns mixColTestInputs'.

Example test_core_mix_cols : toNatState s1 = mixColTest1ExpectedOutput.
Proof. vm_compute. reflexivity. Qed.

(*** Second check with AES256.aes_mix_columns_top_spec. *)

Definition i1 := fromNatVec (transpose mixColTest1InputNat).
Definition s2 := transpose (AES256.aes_mix_columns_circuit_spec false i1).

Example test_aes_spec : toNatVec s2 = mixColTest1ExpectedOutput.
Proof. vm_compute. reflexivity. Qed.

(* A test now with the circuit. *)

Local Open Scope list_scope.

Definition r1L : list (Vector.t (Vector.t (Vector.t bool 8) 4) 4) := combinational (aes_mix_columns [false] [i1]).
Definition o1 := List.hd (defaultCombValue (Vec (Vec (Vec Bit 8) 4) 4)) r1L.

Local Open Scope vector_scope.

Example check_mix_cols_circuit : transpose (toNatVec o1) = mixColTest1ExpectedOutput.
Proof. vm_compute. reflexivity. Qed.

Local Open Scope list_scope.

(* The lemma which needs to be proved to show the Cava mix_colnumns corresponds
   the the specification aes_mix_columns_top_spec.
*)
Lemma aes_mix_columns_correct : forall (op : bool) (i :  Vector.t (Vector.t (Vector.t bool 8) 4) 4),
      combinational (aes_mix_columns [op] [i]) = [aes_mix_columns_circuit_spec op i].
Abort.

Goal
  (let signal := combType in
   (* run encrypt test with this version of aes_mix_columns plugged in *)
   aes_test_encrypt Matrix
                    (fun step key =>
                       match step with
                       | MixColumns =>
                         fun st =>
                           let input := from_flat st in
                           let output := unIdent (aes_mix_columns [false]%list [input]%list) in
                           to_flat (List.hd (defaultCombValue _) output)
                       | _ => aes_impl step key
                       end) = Success).
Proof. vm_compute. reflexivity. Qed.

Goal
  (let signal := combType in
   (* run encrypt test with this version of aes_mix_columns plugged in *)
   aes_test_decrypt Matrix
                    (fun step key =>
                       match step with
                       | InvMixColumns =>
                         fun st =>
                           let input := from_flat st in
                           let output := unIdent (aes_mix_columns [true]%list [input]%list) in
                           to_flat (List.hd (defaultCombValue _) output)
                       | _ => aes_impl step key
                       end) = Success).
Proof. vm_compute. reflexivity. Qed.
