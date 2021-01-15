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
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.NArith.Ndigits.
Import VectorNotations.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Open Scope monad_scope.

Require Import coqutil.Tactics.Tactics.
Require Import Cava.BitArithmetic.
Require Import Cava.NatUtils.
Require Import Cava.ListUtils.
Require Import Cava.VectorUtils.
Require Import Cava.Tactics.

Require Import Cava.Acorn.MonadFacts.
Require Import Cava.Acorn.CombinationalProperties.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.Identity.

Require Import AesSpec.Cipher.
Require Import AesSpec.CipherProperties.
Require Import AesSpec.ExpandAllKeys.
Require Import AesSpec.InterleavedCipher.
Require Import AesSpec.InterleavedInverseCipher.
Require Import AcornAes.CipherRound.

Existing Instance CombinationalSemantics.

Section WithSubroutines.
  Local Notation byte := (Vector.t bool 8).
  Local Notation state := (Vector.t (Vector.t byte 4) 4) (only parsing).
  Local Notation key := (Vector.t (Vector.t byte 4) 4) (only parsing).
  Local Notation round_index := (Vector.t bool 4) (only parsing).
  Local Notation round_constant := byte (only parsing).
  Context (sub_bytes:     list bool -> list state -> ident (list state))
          (shift_rows:    list bool -> list state -> ident (list state))
          (mix_columns:   list bool -> list state -> ident (list state))
          (add_round_key : list key -> list state -> ident (list state))
          (key_expand : list bool -> list round_index -> list key * list round_constant ->
                        ident (list key * list round_constant)).
  Context (sub_bytes_spec shift_rows_spec mix_columns_spec inv_sub_bytes_spec
                          inv_shift_rows_spec inv_mix_columns_spec : state -> state)
          (add_round_key_spec : state -> key -> state)
          (key_expand_spec inv_key_expand_spec :
             nat -> key * round_constant -> key * round_constant).
  Context
    (sub_bytes_correct : forall (is_decrypt : bool) (st : state),
        unIdent (sub_bytes [is_decrypt] [st])
        = [if is_decrypt then inv_sub_bytes_spec st else sub_bytes_spec st])
    (shift_rows_correct : forall (is_decrypt : bool) (st : state),
        unIdent (shift_rows [is_decrypt] [st])
        = [if is_decrypt then inv_shift_rows_spec st else shift_rows_spec st])
    (mix_columns_correct : forall (is_decrypt : bool) (st : state),
        unIdent (mix_columns [is_decrypt] [st])
        = [if is_decrypt then inv_mix_columns_spec st else mix_columns_spec st])
    (add_round_key_correct :
       forall k (st : state), unIdent (add_round_key [k] [st]) = [add_round_key_spec st k])
    (key_expand_correct :
       forall (is_decrypt : bool) (round_i : round_index) (k : key) (rcon : round_constant),
         unIdent (key_expand [is_decrypt] [round_i] ([k],[rcon]))
         = let spec := if is_decrypt then inv_key_expand_spec else key_expand_spec in
           let i := N.to_nat (Bv2N round_i) in
           ([fst (spec i (k, rcon))], [snd (spec i (k, rcon))])).
  Let add_round_key_spec' : state -> key * round_constant -> state :=
    (fun st '(k,_) => add_round_key_spec st k).
  Let inv_mix_columns_key_spec : key * round_constant -> key * round_constant :=
    (fun '(k,rcon) => (inv_mix_columns_spec k, rcon)).

  Hint Rewrite sub_bytes_correct shift_rows_correct mix_columns_correct add_round_key_correct
       key_expand_correct : to_spec.

  Local Ltac simplify_step :=
    first [ destruct_pair_let
          | rewrite N2Nat.id
          | rewrite N2Bv_sized_Bv2N
          | rewrite (pairSel_mkpair (t:=Vec (Vec (Vec Bit 8) 4) 4))
          | progress autorewrite with to_spec
          | progress simpl_ident ]; [ ].
  Local Ltac simplify := repeat simplify_step.

  (* key_expand_and_round is equivalent to interleaved cipher rounds
     (excluding the final round) *)
  Lemma key_expand_and_round_equiv
        (k : key) (rcon : round_constant) (st : state)
        add_round_key_in_sel round_key_sel
        round_i :
    let round := key_expand_and_round
                   (round_index:=Vec Bit 4) (round_constant:=Vec Bit 8)
                   sub_bytes shift_rows mix_columns add_round_key
                   (mix_columns [true])
                   key_expand [false] in
    let round_spec := cipher_round_interleaved
                        add_round_key_spec' sub_bytes_spec shift_rows_spec mix_columns_spec
                        key_expand_spec in
    let i := N.to_nat (Bv2N round_i) in
    add_round_key_in_sel = nat_to_bitvec_sized 2 (if Nat.eqb i 0 then 1 else 0) ->
    round_key_sel = false ->
    unIdent (round ([k], [rcon], [st]) [add_round_key_in_sel] [round_key_sel] [round_i])
    = let '(k',rcon',data') := round_spec (k, rcon, st) i in
      ([k'],[rcon'],[data']).
  Proof.
    cbv zeta; intros. subst_lets. subst.
    cbv [key_expand_and_round cipher_round cipher_round_interleaved mcompose].
    cbv [nat_to_bitvec_sized]. simplify.
    destruct_one_match;
      compute_expr (nat_to_bitvec_sized 2 0);
      compute_expr (nat_to_bitvec_sized 2 1).
    all:rewrite (mux4_mkpair (t:=Vec (Vec (Vec Bit 8) 4) 4)).
    all:simplify.
    all:reflexivity.
  Qed.

  (* key_expand_and_round is equivalent to (inverse) interleaved cipher rounds
     (excluding the final round) *)
  Lemma inverse_key_expand_and_round_equiv
        (k : key) (rcon : round_constant) (st : state)
        add_round_key_in_sel round_key_sel
        round_i :
    let round := key_expand_and_round
                   (round_index:=Vec Bit 4) (round_constant:=Vec Bit 8)
                   sub_bytes shift_rows mix_columns add_round_key
                   (mix_columns [true]) key_expand [true] in
    let round_spec := equivalent_inverse_cipher_round_interleaved
                        add_round_key_spec' inv_sub_bytes_spec inv_shift_rows_spec
                        inv_mix_columns_spec inv_key_expand_spec
                        inv_mix_columns_key_spec in
    let i := N.to_nat (Bv2N round_i) in
    add_round_key_in_sel = nat_to_bitvec_sized 2 (if Nat.eqb i 0 then 1 else 0) ->
    (* round_key_sel is true if this is a "middle round" (in this context, not round 0) *)
    (round_key_sel = if Nat.eqb i 0 then false else true) ->
    unIdent (round ([k], [rcon], [st]) [add_round_key_in_sel] [round_key_sel] [round_i])
    = let '(k',rcon',data') := round_spec (k, rcon, st) i in
      ([k'],[rcon'],[data']).
  Proof.
    cbv zeta; intros. subst_lets. subst.
    cbv [key_expand_and_round
           cipher_round equivalent_inverse_cipher_round_interleaved mcompose].
    cbv [nat_to_bitvec_sized]. simplify.
    repeat destruct_one_match; autorewrite with boolsimpl in *; try congruence.
    all: compute_expr (N2Bv_sized 2 (N.of_nat 0)).
    all: compute_expr (N2Bv_sized 2 (N.of_nat 1)).
    all: rewrite (mux4_mkpair (t:=Vec (Vec (Vec Bit 8) 4) 4)).
    all: autorewrite with vsimpl.
    all: simplify.
    all: reflexivity.
  Qed.

  Lemma key_expand_and_round_last_equiv
        is_decrypt (round_i : round_index) round_key rcon data :
    snd (unIdent
           (key_expand_and_round
              (semantics:=CombinationalSemantics)
              (round_index:=Vec Bit 4) (round_constant:=Vec Bit 8)
              sub_bytes shift_rows mix_columns add_round_key (mix_columns [true])
              key_expand [is_decrypt] ([round_key], [rcon], [data])
              [[false; true]%vector] [false] [round_i]))
    = if is_decrypt
      then [add_round_key_spec (inv_shift_rows_spec (inv_sub_bytes_spec data)) round_key]
      else [add_round_key_spec (shift_rows_spec (sub_bytes_spec data)) round_key].
  Proof.
    cbv [key_expand_and_round mcompose]; intros. subst_lets.
    simplify. rewrite (mux4_mkpair (t:=Vec (Vec (Vec Bit 8) 4) 4)).
    autorewrite with vsimpl. destruct is_decrypt; simplify; reflexivity.
  Qed.

  Lemma cipher_equiv
        (Nr : nat) (init_rcon : round_constant) (round_indices : list (list round_index))
        (num_regular_rounds round0 : round_index)
        (first_key last_key : key) (middle_keys : list key) (input : state) :
    let all_keys_and_rcons := all_keys key_expand_spec Nr (first_key, init_rcon) in
    let all_keys := List.map fst all_keys_and_rcons in
    all_keys = (first_key :: middle_keys ++ [last_key])%list ->
    (* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 ->
    round_indices = map (fun i => [nat_to_bitvec_sized 4 i]) (List.seq 0 (S Nr)) ->
    num_regular_rounds = nat_to_bitvec_sized _ Nr ->
    round0 = nat_to_bitvec_sized _ 0 ->
    unIdent
      (cipher
         (round_index:=Vec Bit 4) (round_constant:=Vec Bit 8)
         sub_bytes shift_rows mix_columns add_round_key (mix_columns [true])
         key_expand [num_regular_rounds] [round0] [false]
         [first_key] [init_rcon] round_indices [input])
    = [Cipher.cipher
         _ _ add_round_key_spec sub_bytes_spec shift_rows_spec mix_columns_spec
         first_key last_key middle_keys input].
  Proof.
    cbv zeta; intro Hall_keys; intros. subst.
    cbv [cipher cipher_step mcompose]. simplify.

    (* Helpful rephrasing of Nr upper bound *)
    assert (N.of_nat Nr < 2 ^ N.of_nat 4)%N
      by (cbn; change (2^4)%nat with 16 in *; Lia.lia).
    pose proof (N.size_nat_le 4 (N.of_nat Nr) ltac:(Lia.lia)).

    (* simplify *)
    cbn [nor2 and2 unpeel CombinationalSemantics]. cbv [lift2].
    cbn [bind ret Monad_ident unIdent].

    (* separate the last round *)
    rewrite foldLM_ident_fold_left.
    autorewrite with pull_snoc natsimpl.

    (* simplify round-index comparisons *)
    rewrite !eqb_nat_to_bitvec_sized, Nat.eqb_refl by Lia.lia.
    match goal with |- context [?n =? 0] => destr (n =? 0); [ Lia.lia | ] end.
    boolsimpl.

    (* Get all states from key expansion *)
    map_inversion Hall_keys; subst.
    match goal with H : @eq (list (_ * _)) _ (_ :: _ ++ [_])%list |- _ =>
                    rename H into Hall_keys end.

    (* representation change; use full key-expansion state (key * round_constant) *)
    erewrite cipher_change_key_rep with (projkey:=@fst key round_constant)
      by reflexivity.

    erewrite <-cipher_interleaved_equiv by eassumption.
    cbv [cipher_interleaved]. repeat destruct_pair_let.

    (* prove using loop invariant *)
    rewrite fold_left_map.
    factor_out_loops.
    eapply fold_left_double_invariant_seq
      with (I:=fun _ x y => y = ([fst (fst x)], [snd (fst x)], [snd x])).
    { (* invariant holds at start of loop *)
      reflexivity. }
    { (* invariant holds through loop body *)
      intros; subst.
      autorewrite with natsimpl in *. repeat destruct_pair_let.
      rewrite !eqb_nat_to_bitvec_sized by Lia.lia.
      erewrite (unpeelVecList_cons_singleton (A:=Bit))
        by first [ Lia.lia | reflexivity
                   | intros *; cbn [InV];
                     autorewrite with vsimpl;
                     intros [? | ?]; [ | tauto];
                     subst; reflexivity ].
      rewrite !pad_combine_eq by length_hammer.
      cbn [combine map].
      rewrite key_expand_and_round_equiv
        by first [ boolsimpl; reflexivity
                 | rewrite nat_to_bitvec_to_nat by Lia.lia;
                   repeat destruct_one_match; (reflexivity || Lia.lia) ].
      rewrite nat_to_bitvec_to_nat by Lia.lia.
      cbv [cipher_round_interleaved].
      repeat destruct_pair_let. subst_lets. cbn [fst snd].
      rewrite <-surjective_pairing.
      reflexivity. }
    { (* invariant implies postcondition *)
      intros; subst. cbn [fst snd].
      erewrite (unpeelVecList_cons_singleton (A:=Bit))
        by first [ Lia.lia | reflexivity
                   | intros *; cbn [InV];
                     autorewrite with vsimpl;
                     intros [? | ?]; [ | tauto];
                     subst; reflexivity ].
      rewrite !pad_combine_eq by length_hammer.
      cbn [combine map fst snd].
      rewrite key_expand_and_round_last_equiv.
      reflexivity. }
  Qed.

  Lemma inv_mix_columns_key_spec_map keys :
    map fst (map inv_mix_columns_key_spec keys) = map inv_mix_columns_spec (map fst keys).
  Proof.
    rewrite !map_map; apply map_ext.
    intros; subst_lets. cbv beta.
    repeat destruct_pair_let; reflexivity.
  Qed.

  Lemma inverse_cipher_equiv
        (Nr : nat) (init_rcon : round_constant) (round_indices : list (list round_index))
        (num_regular_rounds round0 : round_index)
        (first_key last_key : key) (middle_keys : list key) (input : state) :
    let all_keys_and_rcons := all_keys inv_key_expand_spec Nr (first_key, init_rcon) in
    let all_keys := List.map fst all_keys_and_rcons in
    all_keys = (first_key :: middle_keys ++ [last_key])%list ->
    (* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 ->
    round_indices = map (fun i => [nat_to_bitvec_sized 4 i]) (List.seq 0 (S Nr)) ->
    num_regular_rounds = nat_to_bitvec_sized _ Nr ->
    round0 = nat_to_bitvec_sized _ 0 ->
    unIdent
      (cipher
         (round_index:=Vec Bit 4) (round_constant:=Vec Bit 8)
         sub_bytes shift_rows mix_columns add_round_key (mix_columns [true])
         key_expand [num_regular_rounds] [round0] [true]
         [first_key] [init_rcon] round_indices [input])
    = [Cipher.equivalent_inverse_cipher
         _ _ add_round_key_spec inv_sub_bytes_spec inv_shift_rows_spec inv_mix_columns_spec
         first_key last_key (map inv_mix_columns_spec middle_keys) input].
  Proof.
    cbv zeta; intro Hall_keys; intros. subst.
    cbv [cipher cipher_step mcompose]. simplify.

    (* Helpful rephrasing of Nr upper bound *)
    assert (N.of_nat Nr < 2 ^ N.of_nat 4)%N
      by (cbn; change (2^4)%nat with 16 in *; Lia.lia).
    pose proof (N.size_nat_le 4 (N.of_nat Nr) ltac:(Lia.lia)).

    (* simplify *)
    cbn [nor2 and2 unpeel CombinationalSemantics]. cbv [lift2].
    cbn [bind ret Monad_ident unIdent].

    (* separate the last round *)
    rewrite foldLM_ident_fold_left.
    autorewrite with pull_snoc natsimpl.

    (* simplify round-index comparisons *)
    rewrite !eqb_nat_to_bitvec_sized, Nat.eqb_refl by Lia.lia.
    match goal with |- context [?n =? 0] => destr (n =? 0); [ Lia.lia | ] end.
    boolsimpl.

    (* Extract information from key expansion expression *)
    map_inversion Hall_keys. subst.
    match goal with H : @eq (list (_ * _)) _ (_ :: _ ++ [_])%list |- _ =>
                    rename H into Hall_keys end.

    (* representation change; use full key-expansion state (key * round_constant) *)
    erewrite equivalent_inverse_cipher_change_key_rep
      with (projkey:=@fst key round_constant)
           (middle_keys_alt:=List.map inv_mix_columns_key_spec _)
      by (reflexivity || apply inv_mix_columns_key_spec_map).

    erewrite <-equivalent_inverse_cipher_interleaved_equiv by eauto.
    cbv [equivalent_inverse_cipher_interleaved].
    repeat destruct_pair_let.

    (* prove using loop invariant *)
    rewrite fold_left_map.
    factor_out_loops.
    eapply fold_left_double_invariant_seq
      with (I:=fun _ x y => y = ([fst (fst x)], [snd (fst x)], [snd x])).
    { (* invariant holds at start of loop *)
      reflexivity. }
    { (* invariant holds through loop body *)
      intros; subst.
      autorewrite with natsimpl in *. repeat destruct_pair_let.
      rewrite !eqb_nat_to_bitvec_sized by Lia.lia.
      erewrite (unpeelVecList_cons_singleton (A:=Bit))
        by first [ Lia.lia | reflexivity
                   | intros *; cbn [InV];
                     autorewrite with vsimpl;
                     intros [? | ?]; [ | tauto];
                     subst; reflexivity ].
      rewrite !pad_combine_eq by length_hammer.
      cbn [combine map].
      rewrite inverse_key_expand_and_round_equiv
        by first [ boolsimpl; reflexivity
                 | rewrite nat_to_bitvec_to_nat by Lia.lia;
                   repeat destruct_one_match; (reflexivity || Lia.lia) ].
      rewrite nat_to_bitvec_to_nat by Lia.lia.
      cbv [equivalent_inverse_cipher_round_interleaved].
      subst_lets. repeat destruct_pair_let. cbn [fst snd].
      rewrite <-surjective_pairing.
      reflexivity. }
    { (* invariant implies postcondition *)
      intros; subst. cbn [fst snd].
      erewrite (unpeelVecList_cons_singleton (A:=Bit))
        by first [ Lia.lia | reflexivity
                   | intros *; cbn [InV];
                     autorewrite with vsimpl;
                     intros [? | ?]; [ | tauto];
                     subst; reflexivity ].
      rewrite !pad_combine_eq by length_hammer.
      cbn [combine map fst snd].
      rewrite key_expand_and_round_last_equiv.
      reflexivity. }
  Qed.

End WithSubroutines.
