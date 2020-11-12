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

Require Import Coq.Bool.Bvector Coq.Vectors.VectorDef.
Require Import Cava.VectorUtils.

Section Spec.
  (* FIPS 197, 2.1: Word A group of 32 bits that is treated either as a single
     entity or as an array of 4 bytes. *)
  Variable bits_per_word : nat.
  Definition word := (Bvector bits_per_word).

  (* FIPS 197, 2.2: Number of columns (32-bit words) comprising the State.
     For this standard, Nb = 4. *)
  Variable nb : nat.

  Definition state := Vector.t word nb.
  Definition key := word.

  (* FIPS 197, 5.1.4 AddRoundKey() Transformation *)
  Definition add_round_key (input : state) (k : key) : state :=
    map (fun col => BVxor _ col k) input.

  Section Properties.
    Lemma inverse_xorb (b1 : bool) (b2 : bool) : xorb (xorb b1 b2) b2 = b1.
    Proof.
      destruct b1, b2; reflexivity.
    Qed.

    Lemma inverse_bvxor n (a : Vector.t bool n) (b : Vector.t bool n) :
                        BVxor n (BVxor n a b) b = a.
    Proof.
      induction a.
      { eapply case0 with (v:=b). reflexivity. }
      { unfold BVxor.
        do 2 rewrite map2_cons.
        simpl.
        rewrite inverse_xorb.

        unfold BVxor in IHa.
        rewrite IHa.
        reflexivity. }
    Qed.

    Theorem inverse_add_round_key (x : state) (k : key) :
      add_round_key (add_round_key x k) k = x.
    Proof.
      unfold add_round_key.
      cbv [state] in *.
      induction x; [ reflexivity | ].
      { simpl.
        rewrite IHx.
        rewrite inverse_bvxor.
        reflexivity. }
    Qed.
  End Properties.
End Spec.
