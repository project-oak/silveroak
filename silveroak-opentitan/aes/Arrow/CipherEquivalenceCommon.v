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

Require Import Coq.NArith.NArith.
Require Import Coq.Vectors.Vector.
Require Import Cava.Arrow.ArrowKind.
Require Import Cava.VectorUtils.
Import VectorNotations.

Module Notations.
  Notation nat_to_bitvec size n := (Ndigits.N2Bv_sized size (N.of_nat n)).
  Notation nat_to_byte n := (nat_to_bitvec 8 n).
  Notation byte := (Vector.t bool 8) (only parsing).
  Notation state := (Vector.t (Vector.t byte 4) 4) (only parsing).
  Notation key := (Vector.t (Vector.t byte 4) 4) (only parsing).
  Notation rconst := byte (only parsing).
  Notation keypair := (Vector.t (Vector.t byte 4) 8) (only parsing).
End Notations.
Import Notations.

(* aes_key_expand operates on a pair of keys; this is a sliding window of
   (previous key ++ current key). The following definitions project out
   keys from the pair. *)
Definition fstkey : keypair -> key :=
  @slice_by_position
    (t (t bool 8) 4) 8 3 0 (kind_default (Vector (Vector Bit 8) 4)).
Definition sndkey : keypair -> key :=
  @slice_by_position
    (t (t bool 8) 4) 8 7 4 (kind_default (Vector (Vector Bit 8) 4)).

Definition swap_keys (k : keypair) := sndkey k ++ fstkey k.

Lemma sndkey_of_append (v1 v2 : Vector.t _ 4) : sndkey (v1 ++ v2) = v2.
Proof.
  cbv [sndkey slice_by_position]. rewrite !resize_default_id.
  rewrite splitat_append. cbn [fst snd].
  constant_vector_simpl v2. reflexivity.
Qed.

Lemma fstkey_of_append (v1 v2 : Vector.t _ 4) : fstkey (v1 ++ v2) = v1.
Proof. constant_vector_simpl v1. reflexivity. Qed.

Lemma fstkey_sndkey_append kp : fstkey kp ++ sndkey kp = kp.
Proof. constant_vector_simpl kp. reflexivity. Qed.

Lemma swap_keys_involutive kp : swap_keys (swap_keys kp) = kp.
Proof. constant_vector_simpl kp. reflexivity. Qed.

Definition projkey1 (x : rconst * keypair) : key :=
  transpose_rev (fstkey (snd x)).
Definition projkey2 (x : rconst * keypair) : key :=
  transpose_rev (sndkey (snd x)).

(* Adds dummy rconst + other key to a key to create a rconst * keypair *)
Definition unprojkey1 (k : key) : rconst * keypair :=
  (nat_to_byte 0, transpose_rev k ++ const (const (const false 8) 4) 4).
Definition unprojkey2 (k : key) : rconst * keypair :=
  (nat_to_byte 0, const (const (const false 8) 4) 4 ++ transpose_rev k).
Lemma proj_unproj_key1 k : projkey1 (unprojkey1 k) = k.
Proof.
  cbv [projkey1 unprojkey1]. cbn [fst snd].
  rewrite fstkey_of_append.
  apply transpose_rev_involutive.
Qed.

Lemma proj_unproj_key2 k : projkey2 (unprojkey2 k) = k.
Proof.
  cbv [projkey2 unprojkey2]. cbn [fst snd].
  rewrite sndkey_of_append.
  apply transpose_rev_involutive.
Qed.
