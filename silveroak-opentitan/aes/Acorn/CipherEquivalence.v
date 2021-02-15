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
    (fun st k => add_round_key_spec st (fst k)).
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
    lazymatch goal with
    | |- context [(@mux4 _ _ ?t (mkpair (mkpair (mkpair [_] [_]) [_]) [_]) [_])] =>
      rewrite (@mux4_mkpair t)
    | |- context [(@mkpair _ _ ?A ?B [_] [_])] =>
      rewrite (@mkpair_singleton A B)
    | |- context [(@muxPair _ _ ?A [_] ([_], [_]))] =>
      rewrite (@muxPair_correct A)
    | |- context [fst (unpair _)] => rewrite fst_unpair
    | |- context [snd (unpair _)] => rewrite snd_unpair
    | _ => first [ destruct_pair_let
                | rewrite eqb_nat_to_bitvec_sized by Lia.lia
                | rewrite nat_to_bitvec_to_nat by Lia.lia
                | progress simpl_ident
                | progress autorewrite with to_spec
                | progress cbn [fst snd map] ]
    end.
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
    cbv [key_expand_and_round cipher_round_interleaved mcompose
           equivalent_inverse_cipher_round_interleaved ].
    simplify.
    repeat (destruct_one_match || destruct_one_match_hyp);
      try Lia.lia; try congruence.
    all:rewrite <-surjective_pairing.
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
          (fun st i =>
             if i =? Nr
             then last_round_spec is_decrypt st i
             else round_spec is_decrypt st i)
          (List.seq 0 (S Nr)) (first_key, init_rcon, input) in
    tl acc.

  (* Expected trace of the cipher with only the AES state vector recorded *)
  Definition cipher_trace
             (Nr : nat) (is_decrypt : bool) (first_key : key) (init_rcon : round_constant)
             (input : state) : list state :=
    List.map snd (cipher_trace_with_keys Nr is_decrypt first_key init_rcon input).

  (* TODO: move *)
  Lemma in_combine_impl {A B} (a : A) (b : B) l1 l2 :
    In (a,b) (combine l1 l2) -> In a l1 /\ In b l2.
  Proof using Type.
    clear. eauto using in_combine_l, in_combine_r.
  Qed.
  (* TODO: move *)
  Hint Rewrite @combine_nth using solve [length_hammer] : push_nth.
  Hint Rewrite @seq_nth using Lia.lia : push_nth.

  Lemma cipher_loop_equiv
        (Nr : nat) (num_regular_rounds round0 : round_index)
        (is_decrypt : bool) (init_rcon : round_constant)
        (init_key : key) (init_state : state)
        init_key_ init_rcon_ init_state_
        (round_indices : seqType (Vec Bit 4)) :
    (* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 ->
    round_indices = map (nat_to_bitvec_sized 4) (List.seq 0 (S Nr)) ->
    num_regular_rounds = nat_to_bitvec_sized _ Nr ->
    round0 = nat_to_bitvec_sized _ 0 ->
    length init_key_ = Nr ->
    length init_rcon_ = Nr ->
    length init_state_ = Nr ->
    let num_regular_rounds_ : seqType (Vec Bit 4) :=
        repeat num_regular_rounds (S Nr) in
    let round0_ : seqType (Vec Bit 4) :=
        repeat round0 (S Nr) in
    let is_decrypt_ : seqType Bit := repeat is_decrypt (S Nr) in
    let initial_cipher_state
        : seqType (Pair (Pair (Vec (Vec (Vec Bit 8) 4) 4) (Vec Bit 8))
                        (Vec (Vec (Vec Bit 8) 4) 4)) :=
        mkpair (mkpair (init_key :: init_key_) (init_rcon :: init_rcon_))
               (init_state :: init_state_) in
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
    cbv zeta; intros.
    subst round0 num_regular_rounds round_indices.
    cbv [cipher_loop mcompose]. simplify.

    (* simplify loop input *)
    rewrite !pad_combine_eq by length_hammer.
    repeat first [ progress cbn [fst snd]
                 | rewrite combine_repeat_l by length_hammer
                 | rewrite combine_repeat_r by length_hammer
                 | rewrite combine_map_l
                 | rewrite combine_map_r
                 | rewrite map_map ].
    cbn [combine].

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
    2:{ cbn [In]; intros. cbn [combType] in * |- . destruct_products.
        (* forget list lengths (otherwise [subst] substitutes a length expression
           for Nr, which is unpleasant *)
        repeat match goal with
               | H : length _ = Nr |- _ => clear H end.

        (* TODO: factor into two tactics: invert_in and logical_simplify *)
        repeat lazymatch goal with
               | H : In _ (_ :: _) |- _ => cbn [In] in H
               | H : In _ (map _ _) |- _ =>
                 apply in_map_iff in H
               | H : In _ (repeat _ _) |- _ =>
                 apply repeat_spec in H; subst
               | H : In (_,_) (combine _ _) |- _ =>
                 apply in_combine_impl in H
               | H : In _ (seq _ _) |- _ =>
                 apply in_seq in H
               | H : _ /\ _ |- _ => destruct H
               | H : _ \/ _ |- _ => destruct H
               | H : exists _, _ |- _ =>
                 destruct H; destruct_products; cbn [fst snd] in *
               | H : (_, _) = (_,_) |- _ =>
                 inversion H; subst; clear H
               end.
        all:simplify.
        all:rewrite cipher_step_equiv with (Nr:=Nr)
          by (try Lia.lia; repeat destruct_one_match;reflexivity).
        all:repeat (destruct_one_match; try congruence); reflexivity. }
    cbn [combType].
    autorewrite with push_length natsimpl.

    cbv [cipher_trace_with_keys].
    factor_out_loops.
    eapply fold_left_accumulate_double_invariant_seq
      with (I:=fun i (st1 st2 : key * round_constant * state) =>
                 if i =? 0
                 then
                   (* for the first round, st1 is the default value and the loop
                      selects the initial inputs *)
                   st1 = (init_key, init_rcon, init_state)
                 else st1 = st2).
    { reflexivity. }
    { intro i. intros. destruct_products.
      destr (S i =? 0); [ Lia.lia | ].
      cbn [repeat seq combine map]. simplify.
      destr (i =? 0);
        [ subst i; cbn [nth fst snd]; simplify;
          repeat destruct_one_match; try Lia.lia;
          congruence | ].
      destruct i; [ exfalso; Lia.lia | ].
      cbn [nth fst snd].
      erewrite map_nth_inbounds
        with (d2:=(defaultCombValue (Vec Bit 4),
                   (defaultCombValue (Vec (Vec (Vec Bit 8) 4) 4),
                    defaultCombValue (Vec Bit 8),
                    defaultCombValue (Vec (Vec (Vec Bit 8) 4) 4)),
                   0))
        by length_hammer.
      cbn [fst snd combType]. autorewrite with push_nth. cbn [fst snd].
      simplify.
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
    simplify.
    repeat lazymatch goal with
           | |- context [?x =? ?y] =>
             destr (x =? y); try Lia.lia
           | H : context [?x =? ?y] |- _ =>
             destr (x =? y); try Lia.lia
           | H : (_,_) = (_,_) |- _ =>
             inversion H; clear H; subst; cbn [fst snd]
           end; [ ].
    apply list_eq_elementwise; [ length_hammer | ].
    intro j; intros; rewrite !nth_tl.
    autorewrite with push_length in *.
    specialize (Hnth (S j)).
    autorewrite with natsimpl in Hnth.
    repeat destruct_one_match_hyp; try Lia.lia; [ ].
    erewrite Hnth by Lia.lia; reflexivity. }
  Qed.

  Lemma cipher_equiv
        (Nr : nat)
        (init_rcon : seqType (Vec Bit 8))
        (init_key init_state : seqType (Vec (Vec (Vec Bit 8) 4) 4))
        (round_indices : seqType (Vec Bit 4))
        (first_rcon : round_constant)
        (first_key last_key : key) (middle_keys : list key) (input : state) d :
    (* precomputed keys match key expansion *)
    let all_keys_and_rcons := all_keys key_expand_spec Nr (first_key, first_rcon) in
    let all_keys := List.map fst all_keys_and_rcons in
    all_keys = (first_key :: middle_keys ++ [last_key])%list ->
    (* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 ->
    round_indices = map (nat_to_bitvec_sized 4) (List.seq 0 (S Nr)) ->
    (* For the initial state signals, the values are ignored after the first
       round; we only care about the first value and the length *)
    hd (defaultCombValue _) init_key = first_key ->
    hd (defaultCombValue _) init_rcon = first_rcon ->
    hd (defaultCombValue _) init_state = input ->
    length init_key = S Nr ->
    length init_rcon = S Nr ->
    length init_state = S Nr ->
    let num_regular_rounds : seqType (Vec Bit 4) :=
        repeat (nat_to_bitvec_sized _ Nr) (S Nr) in
    let round_0 : seqType (Vec Bit 4) :=
        repeat (nat_to_bitvec_sized _ 0) (S Nr) in
    let is_decrypt : seqType Bit := repeat false (S Nr) in
    (* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 ->
    nth Nr
        (unIdent
           (cipher
              (round_index:=Vec Bit 4) (round_constant:=Vec Bit 8)
              sub_bytes shift_rows mix_columns add_round_key (mix_columns [true])
              key_expand num_regular_rounds round_0 is_decrypt
              init_key init_rcon init_state round_indices)) d
    = AesSpec.Cipher.cipher
        _ _ add_round_key_spec sub_bytes_spec shift_rows_spec mix_columns_spec
        first_key last_key middle_keys input.
  Proof.
    cbv zeta; intro Hall_keys; intros. subst.
    cbv [cipher]. simplify. simpl_ident.

    (* extract first value of initial-state signals *)
    destruct init_key; [ cbn [length] in *; Lia.lia | ].
    destruct init_rcon; [ cbn [length] in *; Lia.lia | ].
    destruct init_state; [ cbn [length] in *; Lia.lia | ].
    cbn [length hd] in *.

    (* use cipher_loop lemma *)
    rewrite cipher_loop_equiv by (try reflexivity; length_hammer).
    cbv [cipher_trace_with_keys]. simplify.

    (* simplify selection of last element *)
    erewrite map_nth_inbounds
      with (d2:=defaultCombValue
                  (Pair (Pair (Vec (Vec (Vec Bit 8) 4) 4) (Vec Bit 8))
                        (Vec (Vec (Vec Bit 8) 4) 4)))
      by length_hammer.
    autorewrite with push_nth. rewrite nth_tl, nth_last by length_hammer.
    rewrite fold_left_accumulate_last.

    (* Get all states from key expansion *)
    map_inversion Hall_keys; subst.
    match goal with H : @eq (list (_ * _)) _ (_ :: _ ++ [_])%list |- _ =>
                    rename H into Hall_keys end.

    (* representation change; use full key-expansion state (key * round_constant) *)
    erewrite cipher_change_key_rep with (projkey:=@fst key round_constant)
      by (reflexivity || eauto).

    erewrite <-cipher_interleaved_equiv by eassumption.
    cbv [cipher_interleaved]. repeat destruct_pair_let.

    (* process last round on LHS *)
    autorewrite with pull_snoc.
    destruct_one_match; try Lia.lia; [ ].

    (* remove the last-round case from loop body *)
    erewrite ListUtils.fold_left_ext_In with (f:= fun _ _ => if _ =? Nr then _ else _)
      by (intros *; rewrite in_seq; intros; repeat destruct_one_match; try Lia.lia;
          reflexivity).

    reflexivity.
  Qed.

  Lemma inv_mix_columns_key_spec_map keys :
    map fst (map inv_mix_columns_key_spec keys) = map inv_mix_columns_spec (map fst keys).
  Proof.
    rewrite !map_map; apply map_ext.
    intros; subst_lets. cbv beta.
    repeat destruct_pair_let; reflexivity.
  Qed.

  Lemma inverse_cipher_equiv
        (Nr : nat)
        (init_rcon : seqType (Vec Bit 8))
        (init_key init_state : seqType (Vec (Vec (Vec Bit 8) 4) 4))
        (round_indices : seqType (Vec Bit 4))
        (first_rcon : round_constant)
        (first_key last_key : key) (middle_keys : list key) (input : state) d :
    (* precomputed keys match key expansion *)
    let all_keys_and_rcons := all_keys inv_key_expand_spec Nr (first_key, first_rcon) in
    let all_keys := List.map fst all_keys_and_rcons in
    all_keys = (first_key :: middle_keys ++ [last_key])%list ->
    (* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 ->
    round_indices = map (nat_to_bitvec_sized 4) (List.seq 0 (S Nr)) ->
    (* For the initial state signals, the values are ignored after the first
       round; we only care about the first value and the length *)
    hd (defaultCombValue _) init_key = first_key ->
    hd (defaultCombValue _) init_rcon = first_rcon ->
    hd (defaultCombValue _) init_state = input ->
    length init_key = S Nr ->
    length init_rcon = S Nr ->
    length init_state = S Nr ->
    let num_regular_rounds : seqType (Vec Bit 4) :=
        repeat (nat_to_bitvec_sized _ Nr) (S Nr) in
    let round_0 : seqType (Vec Bit 4) :=
        repeat (nat_to_bitvec_sized _ 0) (S Nr) in
    let is_decrypt : seqType Bit := repeat true (S Nr) in
    (* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 ->
    nth Nr
        (unIdent
           (cipher
              (round_index:=Vec Bit 4) (round_constant:=Vec Bit 8)
              sub_bytes shift_rows mix_columns add_round_key (mix_columns [true])
              key_expand num_regular_rounds round_0 is_decrypt
              init_key init_rcon init_state round_indices)) d
    = Cipher.equivalent_inverse_cipher
         _ _ add_round_key_spec inv_sub_bytes_spec inv_shift_rows_spec inv_mix_columns_spec
         first_key last_key (map inv_mix_columns_spec middle_keys) input.
  Proof.
    cbv zeta; intro Hall_keys; intros. subst.
    cbv [cipher]. simplify. simpl_ident.

    (* extract first value of initial-state signals *)
    destruct init_key; [ cbn [length] in *; Lia.lia | ].
    destruct init_rcon; [ cbn [length] in *; Lia.lia | ].
    destruct init_state; [ cbn [length] in *; Lia.lia | ].
    cbn [length hd] in *.

    (* use cipher_loop lemma *)
    rewrite cipher_loop_equiv by (try reflexivity; length_hammer).
    cbv [cipher_trace_with_keys]. simplify.

    (* simplify selection of last element *)
    erewrite map_nth_inbounds
      with (d2:=defaultCombValue
                  (Pair (Pair (Vec (Vec (Vec Bit 8) 4) 4) (Vec Bit 8))
                        (Vec (Vec (Vec Bit 8) 4) 4)))
      by length_hammer.
    autorewrite with push_nth. rewrite nth_tl, nth_last by length_hammer.
    rewrite fold_left_accumulate_last.

    (* Get all states from key expansion *)
    map_inversion Hall_keys; subst.
    match goal with H : @eq (list (_ * _)) _ (_ :: _ ++ [_])%list |- _ =>
                    rename H into Hall_keys end.

    (* representation change; use full key-expansion state (key * round_constant) *)
    erewrite equivalent_inverse_cipher_change_key_rep
      with (projkey:=@fst key round_constant)
           (middle_keys_alt:=List.map inv_mix_columns_key_spec _)
      by (reflexivity || apply inv_mix_columns_key_spec_map).

    erewrite <-equivalent_inverse_cipher_interleaved_equiv by eassumption.
    cbv [equivalent_inverse_cipher_interleaved]. repeat destruct_pair_let.

    (* process last round on LHS *)
    autorewrite with pull_snoc.
    destruct_one_match; try Lia.lia; [ ].

    (* remove the last-round case from loop body *)
    erewrite ListUtils.fold_left_ext_In with (f:= fun _ _ => if _ =? Nr then _ else _)
      by (intros *; rewrite in_seq; intros; repeat destruct_one_match; try Lia.lia;
          reflexivity).

    reflexivity.
  Qed.
End WithSubroutines.
