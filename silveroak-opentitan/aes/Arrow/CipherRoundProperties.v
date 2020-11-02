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

From Coq Require Import derive.Derive.
From coqutil Require Import Tactics.Tactics.
From Cava Require Import Arrow.ArrowExport Arrow.DeriveSpec
     Arrow.CombinatorProperties BitArithmetic VectorUtils.
Require Import Cava.Tactics.

From Aes Require Import PkgProperties cipher_round
     mix_columns sbox sub_bytes shift_rows.

Section Wf.
  Context (aes_sub_bytes_Wf : forall sbox_impl, Wf (aes_sub_bytes sbox_impl))
          (aes_shift_rows_Wf : Wf aes_shift_rows)
          (aes_mix_columns_Wf : Wf aes_mix_columns).

  Hint Resolve aes_sub_bytes_Wf aes_shift_rows_Wf aes_mix_columns_Wf : Wf.

  Lemma cipher_round_Wf : forall sbox_impl, Wf (cipher_round sbox_impl).
  Proof. cbv [cipher_round]; prove_Wf. Qed.
  Hint Resolve cipher_round_Wf : Wf.

  Lemma final_cipher_round_Wf :
    forall sbox_impl, Wf (final_cipher_round sbox_impl).
  Proof. cbv [final_cipher_round]; prove_Wf. Qed.
  Hint Resolve final_cipher_round_Wf : Wf.
End Wf.
Hint Resolve cipher_round_Wf final_cipher_round_Wf : Wf.

(* These need to be axioms instead of context variables for
   [autorewrite with kappa_interp] to work as intended *)
Axiom aes_sub_bytes_spec :
  pkg.SboxImpl -> bool -> Vector.t (Vector.t (Vector.t bool 8) 4) 4
  -> Vector.t (Vector.t (Vector.t bool 8) 4) 4.
Axiom aes_shift_rows_spec :
  bool -> Vector.t (Vector.t (Vector.t bool 8) 4) 4
  -> Vector.t (Vector.t (Vector.t bool 8) 4) 4.
Axiom aes_mix_columns_spec :
  bool ->  Vector.t (Vector.t (Vector.t bool 8) 4) 4
  -> Vector.t (Vector.t (Vector.t bool 8) 4) 4.

Section Equivalence.
  Local Notation byte := (Vector.t bool 8) (only parsing).
  Context (aes_sub_bytes_correct :
             forall sbox_impl op_i state,
               kinterp (aes_sub_bytes sbox_impl) (op_i, (state, tt))
               = aes_sub_bytes_spec sbox_impl op_i state)
          (aes_shift_rows_correct :
             forall op_i state,
               kinterp aes_shift_rows (op_i, (state, tt))
               = aes_shift_rows_spec op_i state)
          (aes_mix_columns_correct :
             forall op_i state,
               kinterp mix_columns.aes_mix_columns (op_i, (state, tt))
               = aes_mix_columns_spec op_i state).
  Hint Rewrite @aes_sub_bytes_correct @aes_shift_rows_correct
       @aes_mix_columns_correct : kappa_interp.
  Opaque aes_sub_bytes aes_shift_rows aes_mix_columns.

  Derive cipher_round_spec
         SuchThat (forall (sbox_impl : pkg.SboxImpl) (op_i : bool)
                     (data : Vector.t (Vector.t byte 4) 4)
                     (key : Vector.t (Vector.t byte 4) 4),
                      kinterp (cipher_round sbox_impl)
                              (op_i, (data, (key, tt)))
                      = cipher_round_spec sbox_impl op_i data key)
         As cipher_round_correct.
  Proof.
    cbv [cipher_round]; kappa_spec.
    repeat destruct_pair_let. cbn [fst snd].
    repeat first [derive_foldl_spec | derive_map_spec ].
    derive_spec_done.
  Qed.
  Hint Rewrite @cipher_round_correct : kappa_interp.
  Opaque cipher_round.

  Derive final_cipher_round_spec
         SuchThat (forall (sbox_impl : pkg.SboxImpl) (op_i : bool)
                     (data : Vector.t (Vector.t byte 4) 4)
                     (key : Vector.t (Vector.t byte 4) 4),
                      kinterp (final_cipher_round sbox_impl)
                              (op_i, (data, (key, tt)))
                      = final_cipher_round_spec sbox_impl op_i data key)
         As final_cipher_round_correct.
  Proof.
    cbv [final_cipher_round]; kappa_spec.
    repeat destruct_pair_let. cbn [fst snd].
    repeat first [derive_foldl_spec | derive_map_spec ].
    derive_spec_done.
  Qed.
  Hint Rewrite @final_cipher_round_correct : kappa_interp.
  Opaque final_cipher_round.
End Equivalence.
Hint Rewrite @cipher_round_correct @final_cipher_round_correct
     using solve [eauto] : kappa_interp.
Global Opaque cipher_round final_cipher_round.
