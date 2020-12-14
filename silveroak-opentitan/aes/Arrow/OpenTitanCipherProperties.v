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

Require Import Coq.derive.Derive.
Require Import Cava.Arrow.ArrowExport Cava.Arrow.DeriveSpec
     Cava.Arrow.CombinatorProperties Cava.Tactics.

Require Import Aes.PkgProperties Aes.CipherRoundProperties
     Aes.UnrolledOpenTitanCipher.

Section Wf.
  Context (aes_key_expand_Wf :
             forall sbox_impl, Wf (aes_key_expand sbox_impl))
          (aes_sub_bytes_Wf :
             forall sbox_impl, Wf (SubBytes.aes_sub_bytes sbox_impl))
          (aes_shift_rows_Wf : Wf ShiftRows.aes_shift_rows)
          (aes_mix_columns_Wf : Wf MixColumns.aes_mix_columns).

  Hint Resolve aes_key_expand_Wf aes_sub_bytes_Wf aes_shift_rows_Wf
       aes_mix_columns_Wf : Wf.

  Lemma key_expand_and_round_Wf :
    forall sbox_impl, Wf (key_expand_and_round sbox_impl).
  Proof.
    cbv [key_expand_and_round]; prove_Wf.
    { eapply bitwise_Wf; prove_Wf. }
  Qed.
  Hint Resolve key_expand_and_round_Wf : Wf.

  Lemma unrolled_cipher_Wf :
    forall sbox_impl, Wf (unrolled_cipher sbox_impl).
  Proof. cbv [unrolled_cipher]; prove_Wf. Qed.
  Hint Resolve unrolled_cipher_Wf : Wf.

  Lemma unrolled_cipher_flat_Wf :
    forall sbox_impl, Wf (unrolled_cipher_flat sbox_impl).
  Proof. cbv [unrolled_cipher_flat]; prove_Wf. Qed.
  Hint Resolve unrolled_cipher_flat_Wf : Wf.
End Wf.
Hint Resolve key_expand_and_round_Wf unrolled_cipher_Wf unrolled_cipher_flat_Wf
     : Wf.

Section Equivalence.
  Local Notation byte := (Vector.t bool 8) (only parsing).
  Context (aes_key_expand_spec :
             Pkg.SboxImpl -> bool ->
             Vector.t bool 4 -> byte ->
             Vector.t (Vector.t byte 4) 8 ->
             byte * Vector.t (Vector.t byte 4) 8)
          (aes_key_expand_correct :
             forall sbox_impl op_i round_id rcon key_i,
               kinterp (aes_key_expand sbox_impl)
                       (op_i, (round_id, (rcon, (key_i, tt))))
               = aes_key_expand_spec sbox_impl op_i round_id rcon key_i)
          (aes_sub_bytes_correct :
             forall sbox_impl op_i state,
               kinterp (SubBytes.aes_sub_bytes sbox_impl) (op_i, (state, tt))
               = aes_sub_bytes_spec sbox_impl op_i state)
          (aes_shift_rows_correct :
             forall op_i state,
               kinterp ShiftRows.aes_shift_rows (op_i, (state, tt))
               = aes_shift_rows_spec op_i state)
           (aes_mix_columns_correct :
             forall op_i state,
               kinterp MixColumns.aes_mix_columns (op_i, (state, tt))
               = aes_mix_columns_spec op_i state).
  Hint Rewrite @aes_key_expand_correct @aes_sub_bytes_correct
       @aes_shift_rows_correct @aes_mix_columns_correct : kappa_interp.
  Opaque aes_key_expand MixColumns.aes_mix_columns.

  Derive key_expand_and_round_spec
         SuchThat (forall (sbox_impl : Pkg.SboxImpl)
                     (state : bool * (byte * (Vector.t (Vector.t byte 4) 4
                                           * Vector.t (Vector.t byte 4) 8)))
                     (round : Vector.t bool 4),
                      kinterp (key_expand_and_round sbox_impl)
                              (state, (round, tt))
                      = key_expand_and_round_spec sbox_impl state round)
         As key_expand_and_round_correct.
  Proof.
    cbv [key_expand_and_round]; kappa_spec.
    repeat destruct_pair_let. cbn [fst snd].
    derive_spec_done.
  Qed.
  Hint Rewrite @key_expand_and_round_correct : kappa_interp.
  Opaque key_expand_and_round.

  Derive unrolled_cipher_spec
         SuchThat (forall (sbox_impl : Pkg.SboxImpl) (op_i : bool)
                     (data : Vector.t (Vector.t byte 4) 4)
                     (key : Vector.t (Vector.t byte 4) 8),
                      kinterp (unrolled_cipher sbox_impl)
                              (op_i, (data, (key, tt)))
                      = unrolled_cipher_spec sbox_impl op_i data key)
         As unrolled_cipher_correct.
  Proof.
    cbv [unrolled_cipher]; kappa_spec.
    repeat destruct_pair_let. cbn [fst snd].
    repeat first [derive_foldl_spec | derive_map_spec ].
    derive_spec_done.
  Qed.
  Hint Rewrite @unrolled_cipher_correct : kappa_interp.
  Opaque unrolled_cipher.

  Derive unrolled_cipher_flat_spec
         SuchThat
         (forall sbox_impl op_i (data : Vector.t bool 128) (key : Vector.t bool 256),
            kinterp (unrolled_cipher_flat sbox_impl) (op_i, (data, (key, tt)))
            = unrolled_cipher_flat_spec sbox_impl op_i data key)
         As unrolled_cipher_flat_correct.
  Proof. cbv [unrolled_cipher_flat]. derive_spec. Qed.
  Hint Rewrite @unrolled_cipher_flat_correct : kappa_interp.
  Opaque unrolled_cipher_flat.
End Equivalence.
Hint Rewrite @key_expand_and_round_correct @unrolled_cipher_correct
     @unrolled_cipher_flat_correct using solve [eauto] : kappa_interp.
Global Opaque key_expand_and_round unrolled_cipher unrolled_cipher_flat.
