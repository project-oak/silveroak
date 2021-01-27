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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import Coq.Vectors.Vector.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Arrow.ArrowExport.
Require Import Cava.Arrow.CombinatorProperties.
Require Import Cava.BitArithmetic.
Require Import Cava.NatUtils.
Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
Require Import AesSpec.Cipher.
Require Import AesSpec.CipherProperties.
Require Import AesSpec.ExpandAllKeys.
Require Import AesSpec.InterleavedInverseCipher.
Require Import Aes.CipherEquivalenceCommon
     Aes.OpenTitanCipherProperties Aes.CipherRoundProperties
     Aes.UnrolledOpenTitanCipher.
Import VectorNotations ListNotations.
Import CipherEquivalenceCommon.Notations.

Section Equivalence.
  Context (sbox : Pkg.SboxImpl)
          (aes_key_expand_spec :
             Pkg.SboxImpl -> bool -> Vector.t bool 4 ->
             rconst -> keypair -> rconst * keypair)
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

  Definition add_round_key : state -> key -> state :=
    @bitwise (Vector (Vector (Vector Bit 8) 4) 4) (fun a b => xorb a b).
  Definition inv_sub_bytes : state -> state := aes_sub_bytes_spec sbox true.
  Definition inv_shift_rows : state -> state := aes_shift_rows_spec true.
  Definition inv_mix_columns : state -> state := aes_mix_columns_spec true.

  Definition key_expand : nat -> rconst * keypair -> rconst * keypair :=
    fun i rk => aes_key_expand_spec sbox false (nat_to_bitvec _ i) (fst rk) (snd rk).
  Definition inv_key_expand : nat -> rconst * keypair -> rconst * keypair :=
    fun i rk => aes_key_expand_spec sbox true (nat_to_bitvec _ i) (fst rk) (snd rk).

  Definition loop_states_equivalent
             (impl_loop_state : bool * (rconst * (state * keypair)))
             (spec_loop_state : rconst * keypair * state)
    : Prop :=
    impl_loop_state = (true, (fst (fst spec_loop_state),
                              (snd spec_loop_state,
                               snd (fst spec_loop_state)))).

  Lemma key_expand_and_round_spec_equiv_inverse impl_loop_state spec_loop_state i :
    N.size_nat (N.of_nat i) <= 4 -> (* i must fit in implementation's bitvector size *)
    loop_states_equivalent impl_loop_state spec_loop_state ->
    loop_states_equivalent
      (key_expand_and_round_spec
         aes_key_expand_spec sbox impl_loop_state (nat_to_bitvec _ i))
      (equivalent_inverse_cipher_round_interleaved
        (state:=state) (key:=rconst * keypair)
        (fun st k => add_round_key st (projkey1 k))
        inv_sub_bytes inv_shift_rows inv_mix_columns
        inv_key_expand (fun k => unprojkey1 (inv_mix_columns (projkey1 k)))
        spec_loop_state i).
  Proof.
    cbv [loop_states_equivalent]; intros; subst.
    cbv [key_expand_and_round_spec
           cipher_round_spec equivalent_inverse_cipher_round_interleaved].
    destruct spec_loop_state as [ [ rcon kp ] st]. cbn [fst snd].
    repeat lazymatch goal with
           | |- context [mux (@denote_kind_eqb ?A true false) ?T ?F] =>
             change (mux (@denote_kind_eqb A true false) T F) with F
           end.
    repeat progress
           fold fstkey sndkey inv_mix_columns inv_shift_rows inv_sub_bytes.
    cbv [inv_key_expand add_round_key projkey1 projkey2]. cbn [fst snd].
    rewrite denote_kind_eqb_N2Bv_sized by (cbn; lia).
    replace (N.of_nat i =? 0)%N with (i =? 0)
      by (rewrite N.eqb_compare, N2Nat.inj_compare, !Nat2N.id, <-Nat.eqb_compare;
          reflexivity).
    cbv [unprojkey1]. cbn [fst snd].
    rewrite fstkey_of_append.
    rewrite transpose_rev_involutive.
    reflexivity.
  Qed.

  Lemma last_key_equiv Nr init_rcon init_keypair keys last_key input :
    all_keys key_expand Nr (init_rcon, init_keypair) = (keys ++ [last_key])%list ->
    snd (snd (snd (List.fold_left
                     (fun c a =>
                        key_expand_and_round_spec aes_key_expand_spec sbox c
                                                  (nat_to_bitvec 4 a))
                     (List.seq 0 Nr)
                     (false, (init_rcon, (input, init_keypair))))))
    = (snd last_key).
  Proof.
    intros.
    lazymatch goal with H : ?ks = (_ ++ [last_key])%list |- _ =>
                        replace last_key with (List.last ks (init_rcon, init_keypair))
                          by (rewrite H, last_last; reflexivity)
    end.
    rewrite last_all_keys.
    lazymatch goal with
    | |- snd (snd (snd (@List.fold_left ?A1 nat ?f1 ?ls ?x1)))
        = snd (@List.fold_left ?A2 nat ?f2 ?ls ?x2) =>
      pose (R:=fun (x : A1) (y : A2) =>
                 fst x = false
                 /\ fst (snd x) = fst y
                 /\ snd (snd (snd x)) = snd y);
        assert (R (List.fold_left f1 ls x1) (List.fold_left f2 ls x2))
    end.
    { (* prove that R holds through loop *)
      eapply fold_left_preserves_relation; subst R; [ cbn; tauto | ].
      intros. cbv beta in *. cbv [key_expand key_expand_and_round_spec].
      repeat match goal with H : _ /\ _ |- _ => destruct H end.
      destruct_products. cbn [fst snd] in *. subst.
      tauto. }
    { (* prove that R is strong enough to prove postcondition *)
      subst R. cbv beta in *.
      repeat match goal with H : _ /\ _ |- _ => destruct H end.
      auto. }
  Qed.

  Lemma unrolled_cipher_spec_equiv_inverse
        (Nr:=14) (init_rcon := nat_to_byte 1) (final_rcon:=nat_to_bitvec _ 64)
        init_keypair final_keypair first_key last_key middle_keys input :
    (* key_expand state is rconst * keypair *)
    let all_rcons_and_keypairs_fwd := all_keys key_expand Nr (init_rcon, swap_keys init_keypair) in
    let all_rcons_and_keypairs_inv := all_keys inv_key_expand Nr (final_rcon, swap_keys final_keypair) in
    (* representation change: project out the relevant part of the key and transpose it *)
    let all_keys_fwd := List.map projkey2 all_rcons_and_keypairs_fwd in
    let all_keys_inv := List.map projkey1 all_rcons_and_keypairs_inv in
    all_keys_inv = (first_key :: middle_keys ++ [last_key])%list ->
    (exists keys, all_rcons_and_keypairs_fwd = (keys ++ [(final_rcon, final_keypair)])%list) ->
    unrolled_cipher_spec aes_key_expand_spec sbox true input init_keypair
    = equivalent_inverse_cipher
        state key add_round_key inv_sub_bytes inv_shift_rows inv_mix_columns
        first_key last_key (List.map inv_mix_columns middle_keys) input.
  Proof.
    cbv zeta. cbn [denote_kind] in *. intro Hall_keys. intro Hlast_keys.

    (* Get all states from key expansion *)
    map_inversion Hall_keys; subst.
    match goal with H : @eq (list (_ * keypair)) _ (_ :: _ ++ [_])%list |- _ =>
                    rename H into Hall_keys end.

    destruct Hlast_keys as [? Hlast_keys].

    (* representation change; use full key-expansion state (rconst * keypair) *)
    erewrite equivalent_inverse_cipher_change_key_rep with
        (projkey := projkey1)
        (middle_keys_alt:= List.map (fun x => unprojkey1 x) _);
      [ | reflexivity | reflexivity
        | rewrite List.map_map;
          rewrite List.map_ext with (g:=fun x => x) by auto using proj_unproj_key1;
          rewrite List.map_id; reflexivity ].

    rewrite !List.map_map.

    erewrite <-equivalent_inverse_cipher_interleaved_equiv
      with (inv_key_expand:=inv_key_expand) by eassumption.

    cbv [unrolled_cipher_spec final_cipher_round_spec
                              equivalent_inverse_cipher_interleaved ].
    autorewrite with push_to_list.
    rewrite !fold_left_map with (ls :=List.seq _ _). cbn [fst snd].

    (* select expression for inverse direction by simplifying mux *)
    match goal with
    | |- mux (@denote_kind_eqb ?A true false) _ ?F = ?RHS =>
      change (F = RHS)
    end.

    repeat progress fold fstkey sndkey.
    change (N.to_nat 0) with 0.
    repeat destruct_pair_let. subst Nr.
    repeat match goal with
           | _ => rewrite fstkey_of_append
           | _ => rewrite sndkey_of_append
           | _ => rewrite swap_keys_involutive
           | |- context [sndkey ?k ++ fstkey ?k] =>
             change (sndkey k ++ fstkey k) with (swap_keys k)
           end.

    erewrite last_key_equiv by eassumption.
    cbn [fst snd].

    match goal with
    | |- ?LHS = ?RHS =>
      match LHS with
      | context [ List.fold_left ?f1 ?ls1 ?b1 ] =>
        match RHS with
        | context [ List.fold_left ?f2 ?ls2 ?b2 ] =>
          change ls1 with ls2;
            rewrite (fold_left_preserves_relation_seq
                       (fun _ x y => loop_states_equivalent x y)
                       f1 f2 _ _ b1 b2)
        end
      end
    end; [ | | ].
    { (* equivalence post-loop *)
      cbv [add_round_key projkey1]. cbn [fst snd].
      reflexivity. }
    { (* equivalence at start of loop *)
      reflexivity. }
    { (* equivalence holds through loop body *)
      intros. eapply key_expand_and_round_spec_equiv_inverse; eauto; [ ].
      apply N.size_nat_le. cbn. lia. }
  Qed.
End Equivalence.
