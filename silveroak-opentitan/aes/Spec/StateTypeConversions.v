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

Require Import Coq.Vectors.Vector.
Require Import Cava.BitArithmetic.
Require Import Cava.ListUtils.
Require Import Cava.VectorUtils.

Local Notation byte := Byte.byte (only parsing).
Local Notation state := (Vector.t bool 128) (only parsing).
Local Notation bytes_per_word := 4%nat.
Local Notation bits_per_word := (bytes_per_word * 8)%nat.
Local Notation Nb := 4%nat.

(* Conversions between different representations of the state *)
Section Conversions.
  (* Notes on representation:

     Everything in FIPS is big-endian, while Coq's native bitvectors are
     little-endian. The flat bit-vector for the state is therefore
     little-endian, while rows/columns created from it use the big-endian
     representation.

     For interpretation as a 2-D matrix, bytes in the flat representation are in
     *column-major* order (see FIPS 197 Fig. 3) *)

  Definition to_big_endian_bytes (st : state) : Vector.t byte (bytes_per_word * Nb) :=
    (* byte conversion expects little-endian form *)
    let bytes := bitvec_to_bytevec (bytes_per_word * Nb) st in
    (* reverse to get big-endian *)
    reverse bytes.
  Definition from_big_endian_bytes (bytes : Vector.t byte (bytes_per_word * Nb)) : state :=
    let bytes := reverse bytes in (* change to little-endian *)
    (* byte conversion expects little-endian form *)
    bytevec_to_bitvec _ bytes.

  (* Convert 1-D state to/from 2-D arrays *)
  Definition to_cols (st : state) : Vector.t (Vector.t byte bytes_per_word) Nb :=
    reshape (to_big_endian_bytes st).
  Definition to_rows (st : state) : Vector.t (Vector.t byte Nb) bytes_per_word :=
    transpose (to_cols st).
  Definition from_cols (v : Vector.t (Vector.t byte bytes_per_word) Nb) : state :=
    from_big_endian_bytes (flatten v).
  Definition from_rows (v : Vector.t (Vector.t byte Nb) bytes_per_word) : state :=
    from_cols (transpose v).

  (* Convert state to/from columns, but such that columns are bits (still
     big-endian) instead of bytes *)
  Definition to_cols_bits (st : state) : Vector.t (Vector.t bool bits_per_word) Nb :=
    let cols := to_cols st in
    (* byte conversion expects little-endian form, so reverse each column and
       then reverse back *)
    map (fun c => reverse (bytevec_to_bitvec _ (reverse c))) cols.
  Definition from_cols_bits (bits : Vector.t (Vector.t bool bits_per_word) Nb)
    : state := from_cols (map (fun c => reverse (bitvec_to_bytevec _ (reverse c))) bits).

  (* Convert state to/from columns, but such that bytes are expanded to
     (big-endian) bitvectors. *)
  Definition to_cols_bitvecs (st : state)
    : Vector.t (Vector.t (Vector.t bool 8) bytes_per_word) Nb
   := map reshape (to_cols_bits st).
  Definition from_cols_bitvecs
             (cols : Vector.t (Vector.t (Vector.t bool 8) bytes_per_word) Nb)
    : state := from_cols_bits (map flatten cols).

  (* Convert state to/from rows, but as lists instead of vectors *)
  Definition to_list_rows (st : state) : list (list Byte.byte) :=
    to_list (map to_list (to_rows st)).
  Definition from_list_rows (rows : list (list Byte.byte)) : state :=
    let rows := of_list_sized (@List.nil _) Nb rows in
    let rows := map (of_list_sized Byte.x00 bytes_per_word) rows in
    from_rows rows.
End Conversions.

Section Properties.

  Hint Rewrite @bytevec_to_bitvec_to_bytevec @bitvec_to_bytevec_to_bitvec
       @reverse_reverse @reshape_flatten @flatten_reshape @transpose_involutive
       @of_list_sized_to_list
  : inverse.

  Local Ltac inverse :=
    repeat first [ progress autorewrite with inverse
                 | rewrite map_map
                 | apply map_id_ext; intros
                 | rewrite map_id_ext by (intros; inverse)
                 | reflexivity ].

  Lemma to_big_endian_bytes_from_big_endian_bytes bytes :
    to_big_endian_bytes (from_big_endian_bytes bytes) = bytes.
  Proof.
    cbv [to_big_endian_bytes from_big_endian_bytes].
    inverse.
  Qed.
  Hint Rewrite to_big_endian_bytes_from_big_endian_bytes : inverse.

  Lemma to_cols_from_cols cols :
    to_cols (from_cols cols) = cols.
  Proof. cbv [to_cols from_cols]. inverse. Qed.
  Hint Rewrite to_cols_from_cols : inverse.

  Lemma to_cols_bits_from_cols_bits bits :
    to_cols_bits (from_cols_bits bits) = bits.
  Proof. cbv [to_cols_bits from_cols_bits]. inverse. Qed.
  Hint Rewrite to_cols_bits_from_cols_bits : inverse.

  Lemma to_cols_bitvecs_from_cols_bitvecs bitvecs :
    to_cols_bitvecs (from_cols_bitvecs bitvecs) = bitvecs.
  Proof. cbv [to_cols_bitvecs from_cols_bitvecs]. inverse. Qed.
  Hint Rewrite to_cols_bitvecs_from_cols_bitvecs : inverse.

  Lemma to_rows_from_rows rows :
    to_rows (from_rows rows) = rows.
  Proof. cbv [to_rows from_rows]. inverse. Qed.
  Hint Rewrite to_rows_from_rows : inverse.

  Lemma to_list_rows_from_list_rows rows :
    length rows = bytes_per_word ->
    (forall r, List.In r rows -> length r = Nb) ->
    to_list_rows (from_list_rows rows) = rows.
  Proof.
    intros Hlen_rows Hlen_r.
    cbv [to_list_rows from_list_rows]; intros.
    inverse. cbv [of_list_sized].
    autorewrite with push_to_list.
    erewrite List.map_ext_in
      by (intros; autorewrite with push_to_list;
          reflexivity).
    apply ListUtils.map_id_ext; reflexivity.
  Qed.
  Hint Rewrite to_list_rows_from_list_rows : inverse.

  Lemma to_list_rows_length_outer st :
    length (to_list_rows st) = bytes_per_word.
  Proof.
    cbv [to_list_rows].
    autorewrite with push_length.
    reflexivity.
  Qed.

  Lemma to_list_rows_length_inner st r :
    List.In r (to_list_rows st) -> length r = Nb.
  Proof.
    cbv [to_list_rows]. intro Hin.
    autorewrite with push_to_list in *.
    apply List.in_map_iff in Hin.
    destruct Hin as [? [? ?]]; subst.
    autorewrite with push_length.
    reflexivity.
  Qed.

  Lemma from_big_endian_bytes_to_big_endian_bytes st :
    from_big_endian_bytes (to_big_endian_bytes st) = st.
  Proof.
    cbv [from_big_endian_bytes to_big_endian_bytes].
    inverse.
  Qed.
  Hint Rewrite from_big_endian_bytes_to_big_endian_bytes : inverse.

  Lemma from_cols_to_cols st :
    from_cols (to_cols st) = st.
  Proof. cbv [from_cols to_cols]. inverse. Qed.
  Hint Rewrite from_cols_to_cols : inverse.

  Lemma from_cols_bits_to_cols_bits st :
    from_cols_bits (to_cols_bits st) = st.
  Proof. cbv [from_cols_bits to_cols_bits]. inverse. Qed.
  Hint Rewrite from_cols_bits_to_cols_bits : inverse.

  Lemma from_cols_bitvecs_to_cols_bitvecs st :
    from_cols_bitvecs (to_cols_bitvecs st) = st.
  Proof. cbv [from_cols_bitvecs to_cols_bitvecs]. inverse. Qed.
  Hint Rewrite from_cols_bitvecs_to_cols_bitvecs : inverse.

  Lemma from_rows_to_rows st :
    from_rows (to_rows st) = st.
  Proof. cbv [from_rows to_rows]. inverse. Qed.
  Hint Rewrite from_rows_to_rows : inverse.

  Lemma from_list_rows_to_list_rows st :
    from_list_rows (to_list_rows st) = st.
  Proof. cbv [from_list_rows to_list_rows]. inverse. Qed.
  Hint Rewrite from_list_rows_to_list_rows : inverse.

End Properties.
Hint Rewrite to_big_endian_bytes_from_big_endian_bytes
     from_big_endian_bytes_to_big_endian_bytes
     to_cols_from_cols from_cols_to_cols
     to_cols_bits_from_cols_bits from_cols_bits_to_cols_bits
     to_cols_bitvecs_from_cols_bitvecs from_cols_bitvecs_to_cols_bitvecs
     to_rows_from_rows from_rows_to_rows
     from_list_rows_to_list_rows
     using solve [eauto] : conversions.
Hint Rewrite to_list_rows_from_list_rows
     using solve [length_hammer] : conversions.
Hint Resolve to_list_rows_length_outer
     to_list_rows_length_inner : length.
