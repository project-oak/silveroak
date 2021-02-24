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
Require Import Cava.Acorn.IdentityNew.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Lib.BitVectorOps.
Import ListNotations.

Require Import AesSpec.AES256.
Require Import AesSpec.StateTypeConversions.
Require Import AcornAes.AddRoundKeyCircuit.
Import StateTypeConversions.LittleEndian.

(*
Require Import Psatz.

Existing Instance CombinationalSemantics.
Section Combinators.
  Lemma zipWith_unIdent {A B C : SignalType} n
        (f : seqType A * seqType B -> cava (seqType C))
        (spec : combType A -> combType B -> combType C)
        (va : combType (Vec A n)) (vb : combType (Vec B n)) :
    n <> 0 ->
    (forall a b, unIdent (f ([a], [b])) = [spec a b]) ->
    unIdent (@zipWith _ _ A B C n f [va] [vb])
    = [Vector.map2 spec va vb].
  Proof.
    cbv [zipWith Traversable.mapT Traversable_vector].
    cbn [peel unpeel monad CombinationalSemantics].
    cbn [bind ret Monad_ident unIdent] in *.
    rewrite mapT_vector_ident.
    revert va vb; induction n; intros; [ lia | ].
    { rewrite (eta va), (eta vb).
      autorewrite with push_vcombine push_vector_map vsimpl.
      cbn [combType]  in *. rewrite !peelVecList_cons_cons.
      autorewrite with push_vcombine push_vector_map vsimpl.
      lazymatch goal with
      | Hspec : context [unIdent (f _)] |- _ =>
        rewrite Hspec
      end.
      fold combType.
      destruct (PeanoNat.Nat.eq_dec n 0).
      { subst n. eapply case0 with (v:=Vector.tl va).
        eapply case0 with (v:=Vector.tl vb).
        reflexivity. }
      cbv [seqType].
      erewrite unpeelVecList_cons_singleton; eauto; [ ].
      intros *. rewrite InV_map_iff.
      destruct 1 as [? [? ?]].
      subst.
      cbv [vcombine] in *.
      repeat match goal with
             | H : _ |- _ =>
               apply InV_map2_impl in H; destruct H as [? [? [? [? ?]]]]; subst
             | H : InV _ _ |- _ => apply peelVecList_length in H
             end.
      match goal with
      | |- context [f (?l1, ?l2)] =>
        destruct l1 as [| ? [|? ?] ];
          destruct l2 as [| ? [|? ?] ];
          cbn [length] in *; try lia
      end.
      lazymatch goal with
      | Hspec : context [unIdent (f _)] |- _ =>
        rewrite Hspec
      end.
      reflexivity. }
  Qed.
End Combinators.
 *)

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
    unIdent (aes_add_round_key k st)
    = AES256.aes_add_round_key_circuit_spec k st.
  Proof.
    cbv [AES256.aes_add_round_key_circuit_spec
           AES256.add_round_key
           AddRoundKeyCircuit.aes_add_round_key
           AddRoundKey.add_round_key].
    cbv [xor4x4V xor4xV].
    cbv [Bvector.BVxor xorV].

    rewrite map2_to_cols_bits, map2_to_flat.
    autorewrite with conversions.

    repeat (cbv [zipWith vcombine];
            simpl_ident;
            rewrite map_map2;
            rewrite map2_swap;
            apply map2_ext; intros).

    apply Bool.xorb_comm.
  Qed.
End Equivalence.
