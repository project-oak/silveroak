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

Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Require Import ExtLib.Structures.Monads.
Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
Require Import Cava.Acorn.MonadFacts.
Require Import Cava.Acorn.Identity.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Lib.BitVectorOps.
Import ListNotations.

Require Import AesSpec.AES256.
Require Import AesSpec.StateTypeConversions.
Require Import AcornAes.AddRoundKeyCircuit.
Import StateTypeConversions.LittleEndian.

Existing Instance CombinationalSemantics.

Section Equivalence.
  Local Notation byte := (Vector.t bool 8).
  Local Notation state := (Vector.t (Vector.t byte 4) 4) (only parsing).
  Local Notation key := (Vector.t (Vector.t byte 4) 4) (only parsing).

  Lemma map2_to_flat (f : bool -> bool -> bool) (v1 v2 : state) :
    Vector.map2 f (to_flat v1) (to_flat v2)
    = to_flat (Vector.map2 (Vector.map2 (Vector.map2 f)) v1 v2).
  Proof.
    cbv [to_flat]. cbv [BigEndian.from_rows BigEndian.from_cols].
    cbv [BigEndian.from_big_endian_bytes].
    cbv [BitArithmetic.bytevec_to_bitvec].
    autorewrite with pull_vector_map.
    rewrite !map_map2, !map_map.
    rewrite !map_id_ext
      by (intros; rewrite BitArithmetic.bitvec_to_byte_to_bitvec; reflexivity).
    erewrite map2_ext with
        (f0 := fun a b => BitArithmetic.byte_to_bitvec (BitArithmetic.bitvec_to_byte _))
      by (intros; rewrite BitArithmetic.bitvec_to_byte_to_bitvec; reflexivity).
    autorewrite with pull_vector_map. reflexivity.
  Qed.

  Lemma add_round_key_equiv (k : key) (st : state) :
    combinational (add_round_key [k] [st])
    = [AES256.aes_add_round_key_circuit_spec k st].
  Proof.
    cbv [AES256.aes_add_round_key_circuit_spec
           AES256.add_round_key
           AddRoundKeyCircuit.add_round_key
           AddRoundKey.add_round_key].
    cbv [xor4x4V xor4xV]. cbv [Bvector.BVxor].
    erewrite (zipWith_unIdent (A:=Vec (Vec Bit 8) 4)
                              (B:=Vec (Vec Bit 8) 4)
                              (C:=Vec (Vec Bit 8) 4));
      [ | congruence | ].
    2:{ cbn [fst snd]. intros.
        erewrite (zipWith_unIdent (A:=Vec Bit 8)
                                  (B:=Vec Bit 8)
                                  (C:=Vec Bit 8))
          by first [ congruence
                   | intros; rewrite xorV_unIdent by congruence;
                     reflexivity ].
        reflexivity. }
    f_equal. rewrite map2_to_cols_bits, map2_to_flat.
    autorewrite with conversions.
    do 3 (rewrite map2_swap; apply map2_ext; intros).
    apply Bool.xorb_comm.
  Qed.
End Equivalence.
