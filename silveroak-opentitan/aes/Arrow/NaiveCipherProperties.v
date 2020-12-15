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

Require Import Cava.Arrow.ArrowExport Cava.Arrow.DeriveSpec
        Cava.Arrow.CombinatorProperties.
Require Import Cava.Tactics.

Require Import Aes.PkgProperties Aes.CipherRoundProperties
     Aes.UnrolledNaiveCipher.

Section Wf.
  Context (aes_256_naive_key_expansion_Wf :
             forall sbox_impl, Wf (aes_256_naive_key_expansion sbox_impl))
          (aes_sub_bytes_Wf :
             forall sbox_impl, Wf (SubBytes.aes_sub_bytes sbox_impl))
          (aes_shift_rows_Wf : Wf ShiftRows.aes_shift_rows)
          (aes_mix_columns_Wf : Wf MixColumns.aes_mix_columns).

  Hint Resolve aes_256_naive_key_expansion_Wf aes_sub_bytes_Wf aes_shift_rows_Wf
       aes_mix_columns_Wf : Wf.

  Lemma unrolled_cipher_naive'_Wf :
    forall sbox_impl, Wf (unrolled_cipher_naive' sbox_impl).
  Proof. cbv [unrolled_cipher_naive']; prove_Wf.
    { apply foldl_Wf; prove_Wf. }
    { apply bitwise_Wf; prove_Wf. }
    { apply map_Wf; prove_Wf. }
  Qed.
  Hint Resolve unrolled_cipher_naive'_Wf : Wf.

  Lemma unrolled_cipher_naive_Wf :
    forall sbox_impl, Wf (unrolled_cipher_naive sbox_impl).
  Proof. cbv [unrolled_cipher_naive]; prove_Wf. Qed.
End Wf.

Section Equivalence.
  Local Notation byte := (Vector.t bool 8).
  Context (aes_256_naive_key_expansion_spec :
             Pkg.SboxImpl ->
             Vector.t (Vector.t (Vector.t bool 8) 4) 8 ->
             (Vector.t (Vector.t (Vector.t (Vector.t bool 8) 4) 4) 15))
          (aes_256_naive_key_expansion_correct :
             forall sbox_impl key,
               kinterp (aes_256_naive_key_expansion sbox_impl) (key, tt) =
               aes_256_naive_key_expansion_spec sbox_impl key)
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
  Hint Rewrite @aes_256_naive_key_expansion_correct @aes_sub_bytes_correct
       @aes_shift_rows_correct @aes_mix_columns_correct : kappa_interp.
  Opaque aes_256_naive_key_expansion MixColumns.aes_mix_columns.

  Derive unrolled_cipher_naive'_spec
         SuchThat (forall (sbox_impl : Pkg.SboxImpl) (op_i : bool)
                     (data : Vector.t (Vector.t (Vector.t bool 8) 4) 4)
                     (key : Vector.t (Vector.t (Vector.t bool 8) 4) 8),
                      kinterp (unrolled_cipher_naive' sbox_impl)
                              (op_i, (data, (key, tt)))
                      = unrolled_cipher_naive'_spec sbox_impl op_i data key)
         As unrolled_cipher_naive'_correct.
  Proof.
    cbv [unrolled_cipher_naive']; kappa_spec.
    repeat destruct_pair_let.
    repeat first [derive_foldl_spec | derive_map_spec ].
    derive_spec_done.
  Qed.
  Hint Rewrite @unrolled_cipher_naive'_correct : kappa_interp.
  Opaque unrolled_cipher_naive'.

  Derive unrolled_cipher_naive_spec
         SuchThat
         (forall sbox_impl op_i (data : Vector.t bool 128) (key : Vector.t bool 256),
            kinterp (unrolled_cipher_naive sbox_impl) (op_i, (data, (key, tt)))
            = unrolled_cipher_naive_spec sbox_impl op_i data key)
         As unrolled_cipher_naive_correct.
  Proof. cbv [unrolled_cipher_naive]. derive_spec. Qed.
  Hint Rewrite @unrolled_cipher_naive_correct : kappa_interp.
  Opaque unrolled_cipher_naive.
End Equivalence.
Hint Rewrite @unrolled_cipher_naive'_correct
     @unrolled_cipher_naive_correct using solve [eauto] : kappa_interp.
Global Opaque unrolled_cipher_naive' unrolled_cipher_naive.

