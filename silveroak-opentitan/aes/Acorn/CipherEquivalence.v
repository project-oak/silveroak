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
Require Import Cava.Acorn.SequentialProperties.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.Identity.

Require Import AesSpec.Cipher.
Require Import AesSpec.CipherProperties.
Require Import AesSpec.ExpandAllKeys.
Require Import AesSpec.InterleavedCipher.
Require Import AesSpec.InterleavedInverseCipher.
Require Import AcornAes.Cipher.

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
  Let fwd_round_spec : key * round_constant * state -> nat -> key * round_constant * state :=
    cipher_round_interleaved
      add_round_key_spec' sub_bytes_spec shift_rows_spec mix_columns_spec
      key_expand_spec.
  Let inv_round_spec : key * round_constant * state -> nat -> key * round_constant * state :=
    equivalent_inverse_cipher_round_interleaved
      add_round_key_spec' inv_sub_bytes_spec inv_shift_rows_spec
      inv_mix_columns_spec inv_key_expand_spec
      inv_mix_columns_key_spec.
  Let round_spec (is_decrypt : bool) (key_rcon_data : key * round_constant * state) (i : nat)
    : key * round_constant * state :=
    if is_decrypt then inv_round_spec key_rcon_data i else fwd_round_spec key_rcon_data i.
  Let last_round_spec (is_decrypt : bool) (key_rcon_data : key * round_constant * state) (i : nat)
    : key * round_constant * state :=
    if is_decrypt
    then
      (inv_key_expand_spec i (fst key_rcon_data),
       add_round_key_spec
         (inv_shift_rows_spec (inv_sub_bytes_spec (snd key_rcon_data)))
         (fst (fst key_rcon_data)))
    else
      (key_expand_spec i (fst key_rcon_data),
       add_round_key_spec
         (shift_rows_spec (sub_bytes_spec (snd key_rcon_data)))
         (fst (fst key_rcon_data))).

  Hint Rewrite sub_bytes_correct shift_rows_correct mix_columns_correct add_round_key_correct
       key_expand_correct : to_spec.

  Local Ltac simplify_step :=
    first [ destruct_pair_let
          | rewrite N2Nat.id
          | rewrite N2Bv_sized_Bv2N
          | rewrite (pairSel_mkpair_singleton (t:=Vec (Vec (Vec Bit 8) 4) 4))
          | rewrite fst_unpair
          | rewrite snd_unpair
          | rewrite mkpair_singleton
          | progress cbn [map fst snd]
          | progress autorewrite with to_spec vsimpl
          | progress simpl_ident ]; [ ].
  Local Ltac simplify := repeat simplify_step.

  (* key_expand_and_round is equivalent to interleaved cipher rounds *)
  Lemma key_expand_and_round_equiv
        (is_decrypt : bool)
        (key_rcon_data : key * round_constant * state)
        add_round_key_in_sel round_key_sel
        (i Nr : nat) :
    Nr <> 0 -> i < 2 ^ 4 ->
    add_round_key_in_sel = [Nat.eqb i 0; Nat.eqb i Nr]%vector ->
    (* round_key_sel is true for any "middle round" (not first or last) of an
       inverse cipher *)
    round_key_sel = (if is_decrypt
                     then if Nat.eqb i 0 then false
                          else if Nat.eqb i Nr then false else true
                     else false) ->
    unIdent (key_expand_and_round
                   (round_index:=Vec Bit 4) (round_constant:=Vec Bit 8)
                   sub_bytes shift_rows mix_columns add_round_key
                   (mix_columns [true]) key_expand
                   [is_decrypt] [key_rcon_data] [add_round_key_in_sel] [round_key_sel]
                   [nat_to_bitvec_sized _ i])
    = [if Nat.eqb i Nr
       then last_round_spec is_decrypt key_rcon_data i
       else round_spec is_decrypt key_rcon_data i].
  Proof.
    cbv zeta; intros. subst_lets. subst.
    destruct key_rcon_data as [[round_key rcon] data].
    cbv [key_expand_and_round
           cipher_round cipher_round_interleaved mcompose
           equivalent_inverse_cipher_round_interleaved ].
    simplify. rewrite (mux4_mkpair (t:=Vec (Vec (Vec Bit 8) 4) 4)). simplify.
    repeat destruct_one_match; try Lia.lia.
    all:rewrite (mkpair_singleton (A:=Vec (Vec (Vec Bit 8) 4) 4)
                                  (B:=Vec Bit 8)).
    all:rewrite <-surjective_pairing.
    all:simplify.
    all:rewrite (mkpair_singleton (A:=Pair (Vec (Vec (Vec Bit 8) 4) 4) (Vec Bit 8))
                                  (B:=Vec (Vec (Vec Bit 8) 4) 4)).
    all:rewrite !nat_to_bitvec_to_nat by Lia.lia.
    all:reflexivity.
  Qed.

  Lemma cipher_step_equiv
        (Nr : nat) (is_decrypt is_first_round : bool)
        (num_regular_rounds : round_index)
        (key_rcon_data : key * round_constant * state)
        (i : nat) :
    (* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 -> i <= Nr ->
    num_regular_rounds = nat_to_bitvec_sized _ Nr ->
    is_first_round = (i =? 0)%nat ->
    unIdent
      (cipher_step
         (round_index:=Vec Bit 4) (round_constant:=Vec Bit 8)
         sub_bytes shift_rows mix_columns add_round_key (mix_columns [true])
         key_expand [is_decrypt] [is_first_round] [num_regular_rounds]
         [key_rcon_data] [nat_to_bitvec_sized _ i])
    = [if i =? Nr
       then last_round_spec is_decrypt key_rcon_data i
       else round_spec is_decrypt key_rcon_data i].
  Proof.
    cbv zeta; intro Hall_keys; intros. subst.
    cbv [cipher_step]. simplify.

    (* simplify boolean comparisons *)
    cbn [nor2 and2 CombinationalSemantics].
    cbv [lift2]. simpl_ident.

    rewrite !eqb_nat_to_bitvec_sized by Lia.lia.
    rewrite !pad_combine_eq by reflexivity.
    cbn [map combine fst snd].
    lazymatch goal with
    | |- context [(@unpeel _ _ ?t ?n [[?x]%list;[?y]%list]%vector)] =>
      change (@unpeel _ _ t n [[x]%list;[y]%list]%vector)
        with ([[x;y]%vector]%list); boolsimpl
    end.
    apply key_expand_and_round_equiv with (Nr:=Nr);
      try Lia.lia; repeat destruct_one_match;
        boolsimpl; reflexivity.
  Qed.

  (* Model the expected trace of the cipher loop using the interleaved cipher
     definition *)
  Definition cipher_trace_with_keys
             (Nr : nat) (is_decrypt : bool) (first_key : key) (init_rcon : round_constant)
             (input : state) : list (key * round_constant * state) :=
    (* Run all rounds except the last *)
    let '(acc, state) :=
        fold_left_accumulate
          (round_spec is_decrypt)
          (List.seq 0 Nr) (first_key, init_rcon, input) in
    (tl acc ++ [last_round_spec is_decrypt state Nr]).

  (* Expected trace of the cipher with only the AES state vector recorded *)
  Definition cipher_trace
             (Nr : nat) (is_decrypt : bool) (first_key : key) (init_rcon : round_constant)
             (input : state) : list state :=
    List.map snd (cipher_trace_with_keys Nr is_decrypt first_key init_rcon input).

  Lemma cipher_loop_equiv
        (Nr : nat) (num_regular_rounds round0 : round_index)
        (is_decrypt : bool) (init_rcon : round_constant)
        (init_key : key) (init_state : state)
        (round_indices : seqType (Vec Bit 4)) :
    (* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 ->
    round_indices = map (nat_to_bitvec_sized 4) (List.seq 0 (S Nr)) ->
    num_regular_rounds = nat_to_bitvec_sized _ Nr ->
    round0 = nat_to_bitvec_sized _ 0 ->
    let init_key_ : seqType (Vec (Vec (Vec Bit 8) 4) 4) :=
        repeat init_key (S Nr) in
    let init_rcon_ : seqType (Vec Bit 8) := repeat init_rcon (S Nr) in
    let init_state_ : seqType (Vec (Vec (Vec Bit 8) 4) 4) :=
        repeat init_state (S Nr) in
    let num_regular_rounds_ : seqType (Vec Bit 4) :=
        repeat num_regular_rounds (S Nr) in
    let round0_ : seqType (Vec Bit 4) :=
        repeat round0 (S Nr) in
    let is_decrypt_ : seqType Bit := repeat is_decrypt (S Nr) in
    let initial_cipher_state :=
        mkpair (mkpair init_key_ init_rcon_) init_state_ in
    unIdent
      (cipher_loop
         (round_index:=Vec Bit 4) (round_constant:=Vec Bit 8)
         sub_bytes shift_rows mix_columns add_round_key (mix_columns [true])
         key_expand
         (mkpair (mkpair (mkpair (mkpair num_regular_rounds_ round0_)
                                 is_decrypt_) initial_cipher_state)
                 round_indices))
    = cipher_trace_with_keys Nr is_decrypt init_key init_rcon init_state.
  Proof.
    cbv zeta; intro Hall_keys; intros. subst.
    cbv [cipher_loop mcompose]. simplify.

    (* Helpful rephrasing of Nr upper bound *)
    assert (N.of_nat Nr < 2 ^ N.of_nat 4)%N
      by (cbn; change (2^4)%nat with 16 in *; Lia.lia).
    pose proof (N.size_nat_le 4 (N.of_nat Nr) ltac:(Lia.lia)).

    (* simplify loop input *)
    rewrite !pad_combine_eq by length_hammer.
    repeat first [ progress cbn [fst snd]
                 | rewrite combine_repeat_l by length_hammer
                 | rewrite combine_repeat_r by length_hammer
                 | rewrite combine_map_l
                 | rewrite combine_map_r
                 | rewrite map_map ].

    (* TODO: maybe once round specs are lets we can be explicit about the body here? *)
    (* change to fold_left *)
    let A := lazymatch goal with |- context [(@loopDelayS _ _ _ ?A)] => A end in
    let B := lazymatch goal with |- context [(@loopDelayS _ _ _ _ ?B)] => B end in
    rewrite (@loopDelayS_combinational_body_stepwise_indexed A B)
      with (spec:=fun '(_, _, is_decrypt, init_state, round_i)
                    feedback_state =>
                    let i := N.to_nat (Bv2N round_i) in
                    let st := if i =? 0 then init_state else feedback_state in
                    if i =? Nr
                    then last_round_spec is_decrypt st i
                    else round_spec is_decrypt st i).
    2:{ intros *; rewrite in_map_iff. intros [? [? Hin]].
        rewrite in_seq in Hin. subst. simplify.
        rewrite !eqb_nat_to_bitvec_sized by Lia.lia.
        lazymatch goal with
        | |- context [(@muxPair _ _ ?A [?sel] ([?x], [?y]))] =>
          rewrite (muxPair_correct (t:=A))
        end.
        rewrite cipher_step_equiv with (Nr:=Nr)
          by (try Lia.lia; repeat destruct_one_match;reflexivity).
        rewrite !nat_to_bitvec_to_nat by Lia.lia.
        repeat (destruct_one_match; try congruence);
          reflexivity. }
    autorewrite with push_length.

    (* process last round on LHS *)
    autorewrite with pull_snoc natsimpl.
    rewrite fold_left_accumulate_snoc.
    autorewrite with push_nth push_length natsimpl.

    cbv [cipher_trace_with_keys].
    factor_out_loops.
    eapply fold_left_accumulate_double_invariant_seq
      with (I:=fun i (st1 st2 : key * round_constant * state) =>
                 if i =? 0
                 then
                   (* for the first round, st1 is the default value and the loop
                      selects the initial inputs *)
                   st1 = (init_key, init_rcon, init_state)
                 else if i =? S Nr
                      then
                        (* for the last round, we care only about the state vector *)
                        snd st1 = snd st2
                      else st1 = st2).
    { reflexivity. }
    { intro i. intros. destruct_products.
      destr (S i =? 0); [ Lia.lia | ].
      autorewrite with push_nth natsimpl. cbn [fst snd].
      cbv zeta. rewrite !nat_to_bitvec_to_nat by Lia.lia.
      repeat lazymatch goal with
             | |- context [?x =? ?y] =>
               destr (x =? y); try Lia.lia
             | H : context [?x =? ?y] |- _ =>
               destr (x =? y); try Lia.lia
             | H : (_ , _) = (_ , _) |- _ =>
               inversion H; subst; clear H; cbn [fst snd] in *
             | _ => destruct is_decrypt; reflexivity
             end. }
    { intros *. intros ? Hnth. intros. destruct_products.
      cbn [fst snd combType].
      rewrite !nat_to_bitvec_to_nat by Lia.lia.
      repeat lazymatch goal with
             | |- context [?x =? ?y] =>
               destr (x =? y); try Lia.lia
             | H : context [?x =? ?y] |- _ =>
               destr (x =? y); try Lia.lia
             | H : (_,_) = (_,_) |- _ =>
               inversion H; clear H; subst; cbn [fst snd]
             end; [ ].
      rewrite tl_app by (apply length_pos_nonnil; length_hammer).
      f_equal; [ ].
      apply list_eq_elementwise; [ length_hammer | ].
      intro j; intros; rewrite !nth_tl.
      autorewrite with push_length in *.
      specialize (Hnth (S j)).
      autorewrite with natsimpl in Hnth.
      repeat destruct_one_match_hyp; try Lia.lia; [ ].
      erewrite Hnth by Lia.lia; reflexivity. }
  Qed.

  Lemma cipher_equiv
        (Nr : nat) (init_rcon : round_constant) (round_indices : list round_index)
        (num_regular_rounds round0 : round_index)
        (first_key last_key : key) (middle_keys : list key) (input : state) :
    let all_keys_and_rcons := all_keys key_expand_spec Nr (first_key, init_rcon) in
    let all_keys := List.map fst all_keys_and_rcons in
    all_keys = (first_key :: middle_keys ++ [last_key])%list ->
    (* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 ->
    round_indices = map (nat_to_bitvec_sized 4) (List.seq 0 (S Nr)) ->
    num_regular_rounds = nat_to_bitvec_sized _ Nr ->
    round0 = nat_to_bitvec_sized _ 0 ->
    unIdent
      (cipher
         (round_index:=Vec Bit 4) (round_constant:=Vec Bit 8)
         sub_bytes shift_rows mix_columns add_round_key (mix_columns [true])
         key_expand [num_regular_rounds] [round0] [false]
         [first_key] [init_rcon] round_indices [input])
    = [AesSpec.Cipher.cipher
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
    erewrite loopDelayS_stepwise_indexed
      by (intros; repeat destruct_pair_let; instantiate_app_by_reflexivity).
    autorewrite with push_length pull_snoc natsimpl.
    cbn [fold_left]. autorewrite with push_nth push_length natsimpl.

    (* simplify round-index comparisons *)
    rewrite !eqb_nat_to_bitvec_sized, Nat.eqb_refl by Lia.lia.
    match goal with |- context [?n =? 0] => destr (n =? 0); [ Lia.lia | ] end.
    boolsimpl. rewrite !pad_combine_eq by length_hammer.
    cbn [map combine fst snd norb]. boolsimpl.
    cbn [fold_left]. autorewrite with push_nth push_length natsimpl.
    idtac. cbn [fold_left].
    Set Printing Depth 10000.

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
