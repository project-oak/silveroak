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
Require Import Cava.Arrow.ArrowExport.
Require Import Cava.Arrow.CombinatorProperties.
Require Import Cava.Arrow.DeriveSpec.
Require Import Cava.BitArithmetic.
Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
Require Import AesSpec.Cipher.
Require Import AesSpec.CipherRepresentationChange.
Require Import AesSpec.ExpandAllKeys.
Require Import AesSpec.InterleavedInverseCipher.
From Aes Require Import OpenTitanCipherProperties CipherRoundProperties
     unrolled_opentitan_cipher.
Import VectorNotations ListNotations.

Local Notation nat_to_bitvec size n := (Ndigits.N2Bv_sized size (N.of_nat n)).
Local Notation nat_to_byte n := (nat_to_bitvec 8 n).
Local Notation byte := (Vector.t bool 8) (only parsing).

Section Equivalence.
  Context (sbox : pkg.SboxImpl)
          (aes_key_expand_spec :
             pkg.SboxImpl -> bool -> Vector.t bool 4 -> byte ->
             Vector.t (Vector.t byte 4) 8 ->
             byte * Vector.t (Vector.t byte 4) 8)
          (aes_key_expand_correct :
             forall sbox_impl op_i round_id rcon key_i,
               kinterp (aes_key_expand sbox_impl)
                       (op_i, (round_id, (rcon, (key_i, tt))))
               = aes_key_expand_spec sbox_impl op_i round_id rcon key_i)
          (aes_sub_bytes_correct :
             forall sbox_impl op_i state,
               kinterp (sub_bytes.aes_sub_bytes sbox_impl) (op_i, (state, tt))
               = aes_sub_bytes_spec sbox_impl op_i state)
          (aes_shift_rows_correct :
             forall op_i state,
               kinterp shift_rows.aes_shift_rows (op_i, (state, tt))
               = aes_shift_rows_spec op_i state)
           (aes_mix_columns_correct :
             forall op_i state,
               kinterp mix_columns.aes_mix_columns (op_i, (state, tt))
               = aes_mix_columns_spec op_i state).

  (* We need to know that inverse key expansion is in fact the inverse of
     forward key expansion *)
  Context (inv_key_expand_key_expand :
             forall round_i round_i_inv rcon k,
               let Nr := 14 in
               let nat_to_bitvec sz n := N2Bv_sized sz (N.of_nat n) in
               let rk := aes_key_expand_spec
                           sbox false (nat_to_bitvec _ round_i) rcon k in
               round_i_inv = Nr - S round_i ->
               aes_key_expand_spec
                 sbox true (nat_to_bitvec _ round_i_inv)
                 (fst rk) (snd rk) = (rcon, k)).

  (* TODO: This precondition seems very annoying to prove and is only necessary
     because the implementation plugs in a constant 64 for the first round
     constant of inverse key generation, instead of retrieving the last round
     constant from forward key generation. I can't find any indication that
     OpenTitan does the same; can we change our implementation to remove the
     need for this proof? *)
  Context (last_rcon_equiv
           : forall init_keypair keys last_key,
                 let Nr := 14 in
                 let init_rcon := nat_to_bitvec _ 1 in
                 all_keys (fun i rk => aes_key_expand_spec
                                      sbox false (nat_to_bitvec _ i) (fst rk) (snd rk))
                          Nr (init_rcon, init_keypair) = (keys ++ [last_key])%list ->
                 fst last_key = nat_to_bitvec _ 64).


  Notation state := (Vector.t (Vector.t (Vector.t bool 8) 4) 4) (only parsing).
  Notation key := (Vector.t (Vector.t (Vector.t bool 8) 4) 4) (only parsing).
  Notation rconst := (Vector.t bool 8) (only parsing).
  Notation keypair := (Vector.t (Vector.t (Vector.t bool 8) 4) 8) (only parsing).

  Definition add_round_key : state -> key -> state :=
    @bitwise (Vector (Vector (Vector Bit 8) 4) 4) (fun a b => xorb a b).
  Definition inv_sub_bytes : state -> state := aes_sub_bytes_spec sbox true.
  Definition inv_shift_rows : state -> state := aes_shift_rows_spec true.
  Definition inv_mix_columns : state -> state := aes_mix_columns_spec true.

  Definition key_expand : nat -> rconst * keypair -> rconst * keypair :=
    fun i rk => aes_key_expand_spec sbox false (nat_to_bitvec _ i) (fst rk) (snd rk).
  Definition inv_key_expand : nat -> rconst * keypair -> rconst * keypair :=
    fun i rk => aes_key_expand_spec sbox true (nat_to_bitvec _ i) (fst rk) (snd rk).

  Definition fstkey : keypair -> key :=
    @slice_by_position
      (t (t bool 8) 4) 8 3 0 (kind_default (Vector (Vector Bit 8) 4)).
  Definition sndkey : keypair -> key :=
    @slice_by_position
      (t (t bool 8) 4) 8 7 4 (kind_default (Vector (Vector Bit 8) 4)).

  Definition projkey (x : rconst * keypair) : key :=
    transpose_rev (fstkey (snd x)).

  (* Adds dummy rconst + second key to a key to create a rconst * keypair *)
  Definition mock_extra_key_data (k : key) : rconst * keypair :=
    (nat_to_byte 0, transpose_rev k ++ const (const (const false 8) 4) 4).

  Lemma projkey_mock_id k : projkey (mock_extra_key_data k) = k.
  Proof.
    cbv [projkey mock_extra_key_data fstkey slice_by_position].
    cbn [splitat snd]. rewrite !resize_default_id.
    rewrite splitat_append. cbn [fst].
    apply transpose_rev_involutive.
  Qed.

  Local Ltac constant_vector_simpl vec :=
    lazymatch type of vec with
    | t _ (S ?n) =>
      let v' := fresh "v" in
      rewrite (eta vec); set (v':=tl vec);
      cbv beta in v'; constant_vector_simpl v'
    | t _ 0 => eapply case0 with (v:=vec)
    end.

  (* TODO: refactor into proofs about slice_by_position and append *)
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

  Definition loop_states_equivalent
             (impl_loop_state : bool * (rconst * (state * keypair)))
             (spec_loop_state : rconst * keypair * state)
    : Prop :=
    impl_loop_state = (true, (fst (fst spec_loop_state),
                              (snd spec_loop_state, snd (fst spec_loop_state)))).

  Lemma key_expand_and_round_spec_equiv_inverse impl_loop_state spec_loop_state i :
    N.size_nat (N.of_nat i) <= 4 -> (* i must fit in implementation's bitvector size *)
    loop_states_equivalent impl_loop_state spec_loop_state ->
    loop_states_equivalent
      (key_expand_and_round_spec
         aes_key_expand_spec sbox impl_loop_state (nat_to_bitvec _ i))
      (equivalent_inverse_cipher_round_interleaved
        (state:=state) (key:=rconst * keypair)
        (fun st k => add_round_key st (projkey k))
        inv_sub_bytes inv_shift_rows inv_mix_columns
        inv_key_expand (fun k => mock_extra_key_data (inv_mix_columns (projkey k)))
        spec_loop_state i).
  Proof.
    cbv [loop_states_equivalent]; intros; subst.
    cbv [key_expand_and_round_spec cipher_round_spec
                                   equivalent_inverse_cipher_round_interleaved].
    destruct spec_loop_state as [ [ rcon kp ] st]. cbn [fst snd].
    repeat lazymatch goal with
           | |- context [mux (@denote_kind_eqb ?A true false) ?T ?F] =>
             change (mux (@denote_kind_eqb A true false) T F) with F
           end.
    repeat progress
           fold fstkey sndkey inv_mix_columns inv_shift_rows inv_sub_bytes.
    rewrite projkey_mock_id.
    cbv [inv_key_expand add_round_key projkey]. cbn [fst snd].
    rewrite denote_kind_eqb_N2Bv_sized by (cbn; lia).
    replace (N.of_nat i =? 0)%N with (i =? 0)
      by (rewrite N.eqb_compare, N2Nat.inj_compare, !Nat2N.id, <-Nat.eqb_compare;
          reflexivity).
    reflexivity.
  Qed.

  Lemma last_key_equiv Nr init_rcon init_keypair keys last_key input :
    all_keys key_expand Nr (init_rcon, init_keypair) = (keys ++ [last_key])%list ->
    snd (snd (snd (List.fold_left
                     (fun c a =>
                        key_expand_and_round_spec aes_key_expand_spec sbox c
                                                  (nat_to_bitvec 4 a))
                     (List.seq (N.to_nat 0) Nr)
                     (false, (init_rcon, (input, init_keypair))))))
    = sndkey (snd last_key) ++ fstkey (snd last_key).
  Proof.
  Admitted. (* TODO *)

  Lemma unrolled_cipher_spec_equiv_inverse
        init_keypair first_key last_key middle_keys input :
    let Nr := 14 in
    let init_rcon := nat_to_byte 1 in
    (* for forward direction, reverse keypair so key_expand doesn't have to mux *)
    let init_keypair_rev := sndkey init_keypair ++ fstkey init_keypair in
    (* key_expand state is rconst * keypair *)
    let all_rcons_and_keypairs := all_keys key_expand Nr (init_rcon, init_keypair_rev) in
    (* representation change: project out the forward key and transpose it *)
    let all_keys := List.map projkey all_rcons_and_keypairs in
    all_keys = (first_key :: middle_keys ++ [last_key])%list ->
    unrolled_cipher_spec aes_key_expand_spec sbox true input init_keypair
    = equivalent_inverse_cipher
        state key add_round_key inv_sub_bytes inv_shift_rows inv_mix_columns
        last_key first_key (List.map inv_mix_columns (List.rev middle_keys)) input.
  Proof.
    cbv zeta. cbn [denote_kind] in *. intro Hall_keys.

    (* Get all states from key expansion *)
    map_inversion Hall_keys; subst.
    match goal with H : @eq (list (_ * keypair)) _ (_ :: _ ++ [_])%list |- _ =>
                    rename H into Hall_keys end.

    (* representation change; use full key-expansion state (rconst * keypair) *)
    erewrite equivalent_inverse_cipher_change_key_rep with
        (projkey := projkey)
        (middle_keys_alt:= List.map (fun x => mock_extra_key_data x) _);
      [ | reflexivity | reflexivity
        | rewrite List.map_map;
          rewrite List.map_ext with (g:=fun x => x) by auto using projkey_mock_id;
          rewrite List.map_id; reflexivity ].

    rewrite <-List.map_rev, !List.map_map.
    erewrite <-equivalent_inverse_cipher_interleaved_equiv
      with (inv_key_expand:=inv_key_expand); try eassumption;
      [ | intros; rewrite Hall_keys, app_comm_cons, last_last; reflexivity
        | intros; cbv [key_expand inv_key_expand];
          rewrite inv_key_expand_key_expand;
          solve [auto using surjective_pairing] ].

    cbv [unrolled_cipher_spec final_cipher_round_spec
                              equivalent_inverse_cipher_interleaved ].
    autorewrite with push_to_list.
    rewrite !fold_left_map with (ls :=List.seq _ _). cbn [fst snd].

    (* select expression for inverse direction by simplifying mux *)
    match goal with
    | |- mux (@denote_kind_eqb ?A true false) _ ?F = ?RHS =>
      change (F = RHS)
    end.

    (* The implementation inlines the expression for the last key, which is
       derived from running the entire cipher loop in the forward direction. We
       can use our helper lemma to replace this large expression with the last
       key of all_keys. *)
    erewrite last_key_equiv
      by (rewrite app_comm_cons in Hall_keys; rewrite <-Hall_keys; reflexivity).

    repeat destruct_pair_let.
    repeat progress fold fstkey sndkey.
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
      cbv [add_round_key projkey].
      reflexivity. }
    { (* equivalence at start of loop *)
      cbv [loop_states_equivalent]. cbn [fst snd].
      rewrite sndkey_of_append, fstkey_of_append.
      rewrite fstkey_sndkey_append.
      erewrite last_rcon_equiv by (rewrite app_comm_cons in Hall_keys; eauto).
      reflexivity. }
    { (* equivalence holds through loop body *)
      intros. eapply key_expand_and_round_spec_equiv_inverse; eauto; [ ].
      apply N_size_nat_le. cbn. lia. }
  Qed.
End Equivalence.
