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

From Coq Require Import Arith Eqdep_dec Vector Lia NArith Omega String Ndigits.
From Cava Require Import Arrow.ArrowExport Arrow.CircuitFunctionalEquivalence
     BitArithmetic Tactics VectorUtils.

From ArrowExamples Require Import Aes.pkg Aes.sbox_canright_pkg.

Import VectorNotations.
Import KappaNotation.
Open Scope kind_scope.

(* function automatic logic [3:0] aes_inverse_gf2p4(logic [3:0] gamma);
  logic [3:0] delta;
  logic [1:0] a, b, c, d;
  a          = gamma[3:2] ^ gamma[1:0];
  b          = aes_mul_gf2p2(gamma[3:2], gamma[1:0]);
  c          = aes_scale_omega2_gf2p2(aes_square_gf2p2(a));
  d          = aes_square_gf2p2(c ^ b);
  delta[3:2] = aes_mul_gf2p2(d, gamma[1:0]);
  delta[1:0] = aes_mul_gf2p2(d, gamma[3:2]);
  return delta;
endfunction *)
Program Definition aes_inverse_gf2p4
  :  <<Vector Bit 4, Unit>> ~> (Vector Bit 4) :=
  <[\ gamma =>
      let a = (gamma[:3:2]) ^ (gamma[:1:0]) in
      let b = !aes_mul_gf2p2 (gamma[:3:2]) (gamma[:1:0]) in
      let c = !aes_scale_omega2_gf2p2 (!aes_square_gf2p2 a) in
      let d = !aes_square_gf2p2 (c ^ b) in
      concat
        (!aes_mul_gf2p2 d (gamma[:3:2]))
        (!aes_mul_gf2p2 d (gamma[:1:0]))
  ]>.

  (* // Inverse in GF(2^8), using normal basis [d^16, d]
  // (see Figure 11 in the technical report)
  function automatic logic [7:0] aes_inverse_gf2p8(logic [7:0] gamma);
    logic [7:0] delta;
    logic [3:0] a, b, c, d;
    a          = gamma[7:4] ^ gamma[3:0];
    b          = aes_mul_gf2p4(gamma[7:4], gamma[3:0]);
    c          = aes_square_scale_gf2p4_gf2p2(a);
    d          = aes_inverse_gf2p4(c ^ b);
    delta[7:4] = aes_mul_gf2p4(d, gamma[3:0]);
    delta[3:0] = aes_mul_gf2p4(d, gamma[7:4]);
    return delta;
  endfunction *)
Definition aes_inverse_gf2p8
  :  <<Vector Bit 8, Unit>> ~> (Vector Bit 8) :=
  <[\ gamma =>
      let a = (gamma[:7:4]) ^ (gamma[:3:0]) in
      let b = !aes_mul_gf2p4 (gamma[:7:4]) (gamma[:3:0]) in
      let c = !aes_square_scale_gf2p4_gf2p2 a in
      let d = !aes_inverse_gf2p4 (c ^ b) in

      concat
        (!aes_mul_gf2p4 d (gamma[:7:4]))
        (!aes_mul_gf2p4 d (gamma[:3:0]))
  ]>.

(* module aes_sbox_canright (
  input  aes_pkg::ciph_op_e op_i,
  input  logic [7:0]        data_i,
  output logic [7:0]        data_o
); *)
Definition aes_sbox_canright
  :  << Bit, Vector Bit 8, Unit>> ~> (Vector Bit 8) :=
  <[\ op_i data_i =>
      (* // Convert to normal basis X.
      assign data_basis_x = (op_i == CIPH_FWD) ? aes_mvm(data_i, A2X) :
                                                aes_mvm(data_i ^ 8'h63, S2X); *)
      let data_basis_x = if op_i == !CIPH_FWD
                        then !aes_mvm data_i !A2X
                        else !aes_mvm (data_i ^ #99) !S2X in

      (* // Do the inversion in normal basis X.
      assign data_inverse = aes_inverse_gf2p8(data_basis_x); *)
      let data_inverse = !aes_inverse_gf2p8 data_basis_x in

      (* // Convert to basis S or A.
      assign data_o       = (op_i == CIPH_FWD) ? aes_mvm(data_inverse, X2S) ^ 8'h63 :
                                                aes_mvm(data_inverse, X2A);  *)
      let data_o = if op_i == !CIPH_FWD
                  then (!aes_mvm data_inverse !X2S) ^ #99
                  else !aes_mvm data_inverse !X2A in

      data_o
  ]>.

Definition canright_composed
  :  << Vector Bit 8, Unit>> ~> (Vector Bit 8) :=
  <[\input =>
  let encoded = !aes_sbox_canright !CIPH_FWD input in
  let decoded = !aes_sbox_canright !CIPH_INV encoded in
  decoded ]>.

Require Import Coq.derive.Derive.

Derive CIPH_FWD_spec
       SuchThat (obeys_spec CIPH_FWD CIPH_FWD_spec)
       As CIPH_FWD_correct.
Proof.
  cbv [CIPH_FWD]. circuit_spec.
  subst CIPH_FWD_spec.
  instantiate_app_by_reflexivity.
Qed.

(* This lemma could also be proved the same way as CIPH_FWD *)
Lemma CIPH_INV_correct : obeys_spec CIPH_INV (fun _ : unit => true).
Proof.
  cbv [obeys_spec CIPH_INV]. circuit_spec. reflexivity.
Qed.

(* TODO: fill in these axioms *)
Axiom aes_sbox_canright_spec :
  denote_kind (<<Bit, Vector Bit 8, Unit >>) -> denote_kind (Vector Bit 8).
Axiom aes_sbox_canright_correct :
  obeys_spec aes_sbox_canright aes_sbox_canright_spec.
Axiom CircuitLaws : CategoryLaws CircuitCat.
Existing Instance CircuitLaws.

Hint Resolve aes_sbox_canright_correct CIPH_FWD_correct CIPH_INV_correct
  : circuit_spec_correctness.

Derive canright_composed_spec
       SuchThat (obeys_spec canright_composed canright_composed_spec)
       As canright_composed_correct.
Proof.
  cbv [canright_composed]. circuit_spec.
  subst canright_composed_spec.
  instantiate_app_by_reflexivity.
Qed.
(* Uncomment below to see derived spec for canright_composed *)
(* Print canright_composed_spec. *)

Lemma canright_composed_combinational: is_combinational (closure_conversion aes_sbox_canright).
Proof. time simply_combinational. Qed.

Local Notation "# x" := (nat_to_bitvec_sized 8 x) (at level 99).

Goal interp_combinational (canright_composed _) (# 0) = (# 0).
Proof. time (vm_compute; auto). Qed.

(* TODO(blaxill): reduced bound for CI time *)
Goal forall x, x < 100 ->
interp_combinational (canright_composed _) (#x) = (#x).
Proof. time (repeat (lia || destruct x); now vm_compute). Qed.



