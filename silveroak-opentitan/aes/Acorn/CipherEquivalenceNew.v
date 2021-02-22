(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
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
Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.Circuit.
Require Import Cava.Acorn.Combinational.
Require Import Cava.Acorn.CombinationalPropertiesNew.
Require Import Cava.Acorn.IdentityNew.
Require Import Cava.Acorn.Multistep.

Require Import AesSpec.Cipher.
Require Import AesSpec.CipherProperties.
Require Import AesSpec.ExpandAllKeys.
Require Import AesSpec.InterleavedCipher.
Require Import AesSpec.InterleavedInverseCipher.
Require Import AcornAes.CipherNewLoop.

Existing Instance Combinational.CombinationalSemantics.

Section WithSubroutines.
  Local Notation byte := (Vector.t bool 8).
  Local Notation state := (Vector.t (Vector.t byte 4) 4) (only parsing).
  Local Notation key := (Vector.t (Vector.t byte 4) 4) (only parsing).
  Local Notation round_index := (Vector.t bool 4) (only parsing).
  Local Notation round_constant := byte (only parsing).
  Context (sub_bytes:     bool -> state -> ident state)
          (shift_rows:    bool -> state -> ident state)
          (mix_columns:   bool -> state -> ident state)
          (add_round_key : key -> state -> ident state)
          (key_expand : bool -> round_index -> key * round_constant ->
                        ident (key * round_constant)).
  Context (sub_bytes_spec shift_rows_spec mix_columns_spec inv_sub_bytes_spec
                          inv_shift_rows_spec inv_mix_columns_spec : state -> state)
          (add_round_key_spec : state -> key -> state)
          (key_expand_spec inv_key_expand_spec :
             nat -> key * round_constant -> key * round_constant).
  Context
    (sub_bytes_correct : forall (is_decrypt : bool) (st : state),
        unIdent (sub_bytes is_decrypt st)
        = if is_decrypt then inv_sub_bytes_spec st else sub_bytes_spec st)
    (shift_rows_correct : forall (is_decrypt : bool) (st : state),
        unIdent (shift_rows is_decrypt st)
        = if is_decrypt then inv_shift_rows_spec st else shift_rows_spec st)
    (mix_columns_correct : forall (is_decrypt : bool) (st : state),
        unIdent (mix_columns is_decrypt st)
        = if is_decrypt then inv_mix_columns_spec st else mix_columns_spec st)
    (add_round_key_correct :
       forall k (st : state), unIdent (add_round_key k st) = add_round_key_spec st k)
    (key_expand_correct :
       forall (is_decrypt : bool) (round_i : round_index) (k : key) (rcon : round_constant),
         unIdent (key_expand is_decrypt round_i (k,rcon))
         = let spec := if is_decrypt then inv_key_expand_spec else key_expand_spec in
           let i := N.to_nat (Bv2N round_i) in
           (spec i (k, rcon))).

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
    first [ destruct_pair_let
          | rewrite eqb_nat_to_bitvec_sized by Lia.lia
          | rewrite nat_to_bitvec_to_nat by Lia.lia
          | progress simpl_ident
          | progress autorewrite with to_spec
          | progress cbn [fst snd map] ].
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
               (key:=Vec (Vec (Vec Bit 8) 4) 4)
               (round_constant:=Vec Bit 8)
               (state:=Vec (Vec (Vec Bit 8) 4) 4)
               (round_index:=Vec Bit 4)
               sub_bytes shift_rows mix_columns add_round_key
               (mix_columns true) key_expand
               is_decrypt key_rcon_data add_round_key_in_sel round_key_sel
               (nat_to_bitvec_sized _ i))
    = if Nat.eqb i Nr
      then last_round_spec is_decrypt key_rcon_data i
      else round_spec is_decrypt key_rcon_data i.
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
         (key:=Vec (Vec (Vec Bit 8) 4) 4)
         (round_constant:=Vec Bit 8)
         (state:=Vec (Vec (Vec Bit 8) 4) 4)
         (round_index:=Vec Bit 4)
         sub_bytes shift_rows mix_columns add_round_key (mix_columns true)
         key_expand is_decrypt is_first_round num_regular_rounds
         key_rcon_data (nat_to_bitvec_sized _ i))
    = if i =? Nr
      then last_round_spec is_decrypt key_rcon_data i
      else round_spec is_decrypt key_rcon_data i.
  Proof.
    cbv zeta; intro Hall_keys; intros. subst.
    cbv [cipher_step]. simplify.

    (* simplify boolean comparisons *)
    cbn [nor2 and2 CombinationalSemantics].
    simplify.

    apply key_expand_and_round_equiv with (Nr:=Nr);
      try Lia.lia; repeat destruct_one_match;
        boolsimpl; reflexivity.
  Qed.

  Lemma cipher_loop_step
        (Nr : nat) (num_regular_rounds round0 : round_index)
        (is_decrypt : bool) (init_rcon : round_constant)
        (init_key : key) (init_state : state)
        (round_i : round_index) (i : nat) :
    (* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 ->
    0 <= i <= Nr ->
    num_regular_rounds = nat_to_bitvec_sized _ Nr ->
    round_i = nat_to_bitvec_sized _ i ->
    round0 = nat_to_bitvec_sized _ 0 ->
    let loop := cipher_loop
                  (key:=Vec (Vec (Vec Bit 8) 4) 4)
                  (round_constant:=Vec Bit 8)
                  (state:=Vec (Vec (Vec Bit 8) 4) 4)
                  (round_index:=Vec Bit 4)
                  sub_bytes shift_rows mix_columns add_round_key (mix_columns true)
                  key_expand in
    forall current_state : circuit_state loop,
      let key := snd current_state in
      let rcon := snd (fst current_state) in
      let state := snd (fst (fst current_state)) in
      unIdent
        (interp loop current_state
                (is_decrypt, num_regular_rounds, round0, (init_key, init_rcon, init_state), round_i))
      = let st := if i =? 0 then (init_key, init_rcon, init_state) else (key,rcon,state) in
        let out := (if i =? Nr
                    then last_round_spec is_decrypt st i
                    else round_spec is_decrypt st i) in
        (out, (tt, snd out, snd (fst out), fst (fst out))).
  Proof.
    cbv zeta; intros.
    subst round0 num_regular_rounds round_i.
    cbv [cipher_loop Loop] in *. cbn [interp circuit_state] in *.
    destruct_products. repeat destruct_pair_let. cbn [fst snd].
    simpl_ident. rewrite !eqb_nat_to_bitvec_sized by Lia.lia.
    rewrite cipher_step_equiv with (Nr:=Nr)
      by (try Lia.lia; destruct i; reflexivity).
    (* too many pair-lets to simplify them all straightaway; expose pairs first *)
    destruct_inner_pair_let; cbn [unIdent].
    destruct_inner_pair_let; cbn [unIdent].
    simplify.
    repeat destruct_one_match; cbn [fst snd].
    all:rewrite <-!surjective_pairing.
    all:try Lia.lia.
    all:try reflexivity.
    all:exfalso; congruence.
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

  Lemma cipher_loop_equiv
        (Nr : nat) (is_decrypt : bool)
        (init_rcon : round_constant) (init_key : key) (init_state : state)
        (cipher_input : list _) :
    (* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 ->
    let init_cipher_state := (init_key, init_rcon, init_state) in
    cipher_input = map
                     (fun i =>
                        (is_decrypt, nat_to_bitvec_sized _ Nr,
                         nat_to_bitvec_sized _ 0, init_cipher_state,
                         nat_to_bitvec_sized _ i))
                     (seq 0 (S Nr)) ->
    let loop := cipher_loop
                  (key:=Vec (Vec (Vec Bit 8) 4) 4)
                  (round_constant:=Vec Bit 8)
                  (state:=Vec (Vec (Vec Bit 8) 4) 4)
                  (round_index:=Vec Bit 4)
                  sub_bytes shift_rows mix_columns add_round_key (mix_columns true)
                  key_expand in
    multistep loop cipher_input
    = cipher_trace_with_keys Nr is_decrypt init_key init_rcon init_state.
  Proof.
    cbv zeta; intros. subst cipher_input.
    cbv [multistep cipher_trace_with_keys].
    cbn [seq map].
    rewrite fold_left_accumulate_cons_full.
    cbn [tl].

    (* simplify first step *)
    rewrite cipher_loop_step with (Nr:=Nr) (i:=0)
      by (reflexivity || Lia.lia).
    cbv zeta. rewrite Nat.eqb_refl.
    destr (0 =? Nr); [ exfalso; Lia.lia | ].
    repeat destruct_pair_let. cbn [fst snd].

    (* Use loop invariant *)
    rewrite fold_left_accumulate_map.
    factor_out_loops.
    eapply fold_left_accumulate_double_invariant_seq
      with (I:=fun i st1 st2 => (st1 = (st2, (tt, snd st2, snd (fst st2), fst (fst st2))))).
    { (* invariant holds at start *)
      reflexivity. }
    { (* invariant holds through body *)
      intro i; intros. subst. cbn [fst snd].
      erewrite cipher_loop_step with (Nr:=Nr) (i:=i)
        by (reflexivity || Lia.lia).
      cbn zeta delta [fst snd]. repeat destruct_pair_let.
      cbn [fst snd]. destr (i =? 0); [ Lia.lia | ].
      destruct_products. cbn [fst snd].
      destr (i =? Nr); reflexivity. }
    { (* invariant implies postcondition *)
      intros; subst. cbn [fst snd].
      cbn [circuit_state Loop cipher_loop] in *.
      apply list_eq_elementwise; [ cbn; length_hammer | ].
      intro j; autorewrite with push_length; intros.
      rename H1 into Hnth. (* TODO:change *)
      specialize (Hnth (S j)).
      autorewrite with natsimpl in Hnth.

      (* generate a new default element and use it to rewrite with map_nth_inbounds *)
      let d := fresh "d" in
      lazymatch goal with
      | |- context [nth _ (@map ?A _ _ _) _] =>
        assert A as d
            by (destruct_products;
                repeat lazymatch goal with
                       | |- (_ * _)%type => refine (_,_)
                       | |- unit => exact tt
                       | _ => eassumption
                       end)
      end;
        rewrite map_nth_inbounds with (d2:=d) by Lia.lia.
      erewrite Hnth by (cbn [combType] in *; Lia.lia).
      reflexivity. }
  Qed.

  Lemma cipher_equiv
        (Nr : nat) (init_rcon : round_constant) (init_key : key) (init_state : state)
        (last_key : key) (middle_keys : list key)
        (cipher_input : list _) :
    (* precomputed keys match key expansion *)
    let all_keys_and_rcons := all_keys key_expand_spec Nr (init_key, init_rcon) in
    let all_keys := List.map fst all_keys_and_rcons in
    all_keys = (init_key :: middle_keys ++ [last_key])%list ->
    (* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 ->
    let init_cipher_state := (init_key, init_rcon, init_state) in
    cipher_input = map
                     (fun i =>
                        (false, nat_to_bitvec_sized _ Nr,
                         nat_to_bitvec_sized _ 0, init_cipher_state,
                         nat_to_bitvec_sized _ i))
                     (seq 0 (S Nr)) ->
    let cipher := cipher
                    (key:=Vec (Vec (Vec Bit 8) 4) 4)
                    (round_constant:=Vec Bit 8)
                    (state:=Vec (Vec (Vec Bit 8) 4) 4)
                    (round_index:=Vec Bit 4)
                    sub_bytes shift_rows mix_columns add_round_key (mix_columns true)
                    key_expand in
    forall d,
      nth Nr (multistep cipher cipher_input) d
      = AesSpec.Cipher.cipher
          _ _ add_round_key_spec sub_bytes_spec shift_rows_spec mix_columns_spec
          init_key last_key middle_keys init_state.
  Proof.
    cbv zeta; intro Hall_keys; intros. subst.
    cbv [cipher]. rewrite multistep_compose, multistep_comb.
    erewrite map_ext with (g:=snd) by (intros; destruct_products; reflexivity).
    erewrite cipher_loop_equiv with (Nr:=Nr) by (assumption||reflexivity).
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
        (Nr : nat) (init_rcon : round_constant) (init_key : key) (init_state : state)
        (last_key : key) (middle_keys : list key)
        (cipher_input : list _) :
    (* precomputed keys match key expansion *)
    let all_keys_and_rcons := all_keys inv_key_expand_spec Nr (init_key, init_rcon) in
    let all_keys := List.map fst all_keys_and_rcons in
    all_keys = (init_key :: middle_keys ++ [last_key])%list ->
    (* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 ->
    let init_cipher_state := (init_key, init_rcon, init_state) in
    cipher_input = map
                     (fun i =>
                        (true, nat_to_bitvec_sized _ Nr,
                         nat_to_bitvec_sized _ 0, init_cipher_state,
                         nat_to_bitvec_sized _ i))
                     (seq 0 (S Nr)) ->
    let cipher := cipher
                    (key:=Vec (Vec (Vec Bit 8) 4) 4)
                    (round_constant:=Vec Bit 8)
                    (state:=Vec (Vec (Vec Bit 8) 4) 4)
                    (round_index:=Vec Bit 4)
                    sub_bytes shift_rows mix_columns add_round_key (mix_columns true)
                    key_expand in
    forall d,
      nth Nr (multistep cipher cipher_input) d
      = Cipher.equivalent_inverse_cipher
         _ _ add_round_key_spec inv_sub_bytes_spec inv_shift_rows_spec inv_mix_columns_spec
         init_key last_key (map inv_mix_columns_spec middle_keys) init_state.
  Proof.
    cbv zeta; intro Hall_keys; intros. subst.
    cbv [cipher]. rewrite multistep_compose, multistep_comb.
    erewrite map_ext with (g:=snd) by (intros; destruct_products; reflexivity).
    erewrite cipher_loop_equiv with (Nr:=Nr) by (assumption||reflexivity).
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
