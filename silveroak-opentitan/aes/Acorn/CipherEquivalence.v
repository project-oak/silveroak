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

Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.Circuit.
Require Import Cava.Acorn.Combinational.
Require Import Cava.Acorn.CombinationalProperties.
Require Import Cava.Acorn.Identity.
Require Import Cava.Acorn.Multistep.

Require Import AesSpec.Cipher.
Require Import AesSpec.CipherProperties.
Require Import AcornAes.CipherCircuit.

Existing Instance Combinational.CombinationalSemantics.

Local Notation byte := (Vector.t bool 8).
Local Notation state := (Vector.t (Vector.t byte 4) 4) (only parsing).
Local Notation key := (Vector.t (Vector.t byte 4) 4) (only parsing).
Local Notation round_index := (Vector.t bool 4) (only parsing).

(* Helper definition to package the signals needed by the cipher loop *)
Definition make_cipher_signals (Nr : nat) (is_decrypt : bool)
           (init_state_input : list state) :
  list (bool * round_index * round_index * round_index * state) :=
  (* assemble constant values + round index *)
  let inner := map (fun i =>
                      (is_decrypt, nat_to_bitvec_sized _ Nr,
                       nat_to_bitvec_sized _ 0, nat_to_bitvec_sized _ i))
                   (seq 0 (S Nr)) in
  (* combine with initial key and initial state *)
  combine inner init_state_input.

Lemma make_cipher_signals_length Nr is_decrypt init_state_input :
  length init_state_input = S Nr ->
  length (make_cipher_signals
            Nr is_decrypt init_state_input) = S Nr.
Proof. intros; cbv [make_cipher_signals]. length_hammer. Qed.
Hint Rewrite @make_cipher_signals_length using solve [length_hammer] : push_length.

Section WithSubroutines.
  Context (sub_bytes:     bool -> state -> ident state)
          (shift_rows:    bool -> state -> ident state)
          (mix_columns:   bool -> state -> ident state)
          (add_round_key : key -> state -> ident state).
  Context (sub_bytes_spec shift_rows_spec mix_columns_spec inv_sub_bytes_spec
                          inv_shift_rows_spec inv_mix_columns_spec : state -> state)
          (add_round_key_spec : state -> key -> state).
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
       forall k (st : state), unIdent (add_round_key k st) = add_round_key_spec st k).

  (* Formula for each round based on index *)
  Let round_spec (Nr : nat) (is_decrypt : bool) (k : key) (st : state) (i : nat) : state :=
    if i =? 0
    then add_round_key_spec st k
    else if is_decrypt
         then if i =? Nr
              then add_round_key_spec (inv_shift_rows_spec (inv_sub_bytes_spec st)) k
              else add_round_key_spec
                     (inv_mix_columns_spec (inv_shift_rows_spec (inv_sub_bytes_spec st)))
                     (inv_mix_columns_spec k)
         else if i =? Nr
              then add_round_key_spec (shift_rows_spec (sub_bytes_spec st)) k
              else add_round_key_spec
                     (mix_columns_spec (shift_rows_spec (sub_bytes_spec st))) k.

  Hint Rewrite sub_bytes_correct shift_rows_correct mix_columns_correct add_round_key_correct
       : to_spec.

  Local Ltac simplify_step :=
    first [ destruct_pair_let
          | rewrite eqb_nat_to_bitvec_sized by Lia.lia
          | rewrite nat_to_bitvec_to_nat by Lia.lia
          | progress simpl_ident
          | progress autorewrite with to_spec
          | progress cbn [fst snd map] ].
  Local Ltac simplify := repeat simplify_step.

  Lemma cipher_round_equiv
        (is_decrypt : bool) (k : key) (data : state)
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
    unIdent (cipher_round
               (key:=Vec (Vec (Vec Bit 8) 4) 4)
               (state:=Vec (Vec (Vec Bit 8) 4) 4)
               (round_index:=Vec Bit 4)
               sub_bytes shift_rows mix_columns add_round_key (mix_columns true)
               is_decrypt k add_round_key_in_sel round_key_sel
               (nat_to_bitvec_sized _ i) data)
    = round_spec Nr is_decrypt k data i.
  Proof.
    cbv zeta; intros. subst_lets. subst. destruct_products.
    cbv [cipher_round mcompose]. simplify.
    repeat (destruct_one_match || destruct_one_match_hyp);
      try Lia.lia; try congruence; reflexivity.
  Qed.

  Lemma cipher_step_equiv
        (Nr : nat) (is_decrypt is_first_round : bool)
        (num_regular_rounds : round_index) (k : key) (data : state)
        (i : nat) :
    (* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 -> i <= Nr ->
    num_regular_rounds = nat_to_bitvec_sized _ Nr ->
    is_first_round = (i =? 0)%nat ->
    unIdent
      (cipher_step
         (key:=Vec (Vec (Vec Bit 8) 4) 4)
         (state:=Vec (Vec (Vec Bit 8) 4) 4)
         (round_index:=Vec Bit 4)
         sub_bytes shift_rows mix_columns add_round_key (mix_columns true)
         is_decrypt is_first_round num_regular_rounds
         k (nat_to_bitvec_sized _ i) data)
    = round_spec Nr is_decrypt k data i.
  Proof.
    cbv zeta; intro Hall_keys; intros. subst.
    cbv [cipher_step]. simplify. destruct_products.

    (* simplify boolean comparisons *)
    cbn [nor2 and2 CombinationalSemantics].
    simplify.

    apply cipher_round_equiv with (Nr:=Nr);
      try Lia.lia; repeat destruct_one_match;
        boolsimpl; reflexivity.
  Qed.

  Lemma cipher_loop_step
        (Nr : nat) (num_regular_rounds round0 : round_index)
        (is_decrypt : bool) (init_state : state)
        (round_key : key) (round_i : round_index) (i : nat) :
    (* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 ->
    0 <= i <= Nr ->
    num_regular_rounds = nat_to_bitvec_sized _ Nr ->
    round_i = nat_to_bitvec_sized _ i ->
    round0 = nat_to_bitvec_sized _ 0 ->
    let loop := cipher_loop
                  (key:=Vec (Vec (Vec Bit 8) 4) 4)
                  (state:=Vec (Vec (Vec Bit 8) 4) 4)
                  (round_index:=Vec Bit 4)
                  sub_bytes shift_rows mix_columns add_round_key (mix_columns true) in
    forall current_state : circuit_state loop,
      step loop current_state
           (is_decrypt, num_regular_rounds, round0, round_i, init_state, round_key)
      = let st := if i =? 0 then init_state else snd (snd (current_state)) in
        let st' := round_spec Nr is_decrypt round_key st i in
        (st', (tt, (tt, st'))).
  Proof.
    cbv zeta; intros.
    subst round0 num_regular_rounds round_i.
    cbv [cipher_loop Loop] in *. cbn [step circuit_state] in *.
    destruct_products. simplify.
    rewrite cipher_step_equiv with (Nr:=Nr)
      by (try Lia.lia; destruct i; reflexivity).
    simplify.
    repeat destruct_one_match; cbn [fst snd].
    all:try Lia.lia.
    all:try reflexivity.
    all:exfalso; congruence.
  Qed.

  (* Model the expected trace of the cipher loop *)
  Definition cipher_trace_with_keys
             (Nr : nat) (is_decrypt : bool)
             (init_state : state) (round_keys : list key) : list state :=
    (* Run all rounds except the last *)
    let '(acc, state) :=
        fold_left_accumulate
          (fun st '(i,k) =>
             round_spec Nr is_decrypt k st i)
          (combine (List.seq 0 (S Nr)) round_keys)
          init_state in
    tl acc.

  Lemma cipher_loop_equiv
        (Nr : nat) (is_decrypt : bool)
        (init_state : state) init_state_ignored
        (round_keys : list key) (cipher_input : list _) :
    (* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 ->
    length init_state_ignored = Nr ->
    length round_keys = S Nr ->
    cipher_input = make_cipher_signals
                     Nr is_decrypt
                     (init_state :: init_state_ignored) ->
    let loop := cipher_loop
                  (key:=Vec (Vec (Vec Bit 8) 4) 4)
                  (state:=Vec (Vec (Vec Bit 8) 4) 4)
                  (round_index:=Vec Bit 4)
                  sub_bytes shift_rows mix_columns add_round_key (mix_columns true) in
    multistep loop (combine cipher_input round_keys)
    = cipher_trace_with_keys Nr is_decrypt init_state round_keys.
  Proof.
    cbv zeta; intros. subst cipher_input.
    cbv [make_cipher_signals] in *.
    destruct round_keys; cbn [length] in *; [ length_hammer | ].
    cbv [multistep cipher_trace_with_keys].
    cbn [seq map combine].
    rewrite fold_left_accumulate_cons_full.
    cbn [tl].

    (* simplify first step *)
    rewrite cipher_loop_step with (Nr:=Nr) (i:=0)
      by (reflexivity || Lia.lia).
    cbv zeta. rewrite Nat.eqb_refl.
    destr (0 =? Nr); [ exfalso; Lia.lia | ].
    repeat destruct_pair_let. cbn [fst snd].

    (* Use loop invariant *)
    rewrite fold_left_accumulate_to_seq
      with (default := (defaultCombValue _, defaultCombValue _, defaultCombValue _,
                        defaultCombValue _, defaultCombValue _, defaultCombValue _)).
    rewrite fold_left_accumulate_to_seq
      with (default:=(0,defaultCombValue (Vec (Vec (Vec Bit 8) 4) 4))).
    autorewrite with push_length natsimpl.
    factor_out_loops.
    eapply fold_left_accumulate_double_invariant_seq
      with (I:=fun i st1 st2 => (st1 = (st2, (tt, (tt, st2))))).
    { (* invariant holds at start *)
      reflexivity. }
    { (* invariant holds through body *)
      intros i x y; intros; subst x. cbn [fst snd].
      rewrite <-!seq_shift, !map_map.
      rewrite !combine_map_l.
      erewrite map_nth_inbounds with (d2:=(0,init_state,init_state)) by length_hammer.
      erewrite map_nth_inbounds with (d2:=(0,init_state)) by length_hammer.
      cbn [combType] in *.
      autorewrite with push_nth natsimpl. cbn [fst snd].
      erewrite cipher_loop_step with (Nr:=Nr) (i:=S i)
        by (reflexivity || Lia.lia).
      cbn [fst snd]. repeat destruct_pair_let.
      cbn [fst snd]. change (S i =? 0) with false. cbn match.
      destruct_products. reflexivity. }
    { (* invariant implies postcondition *)
      intros *. intros Heq Hnth; intros.
      rewrite Heq in *. cbn [fst snd].
      cbn [circuit_state Loop cipher_loop] in *.
      apply list_eq_elementwise; [ cbn; length_hammer | ].
      intro j; autorewrite with push_length.
      specialize (Hnth j).
      autorewrite with natsimpl in Hnth; intros.

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

  Lemma fold_round_spec_equiv (Nr : nat) (is_decrypt : bool)
        init_key init_state middle_keys last_key :
    0 < Nr ->
    length middle_keys = Nr - 1 ->
    fold_left (fun (st : t (t byte 4) 4) '(i, k) => round_spec Nr is_decrypt k st i)
              (combine (seq 1 Nr) (middle_keys ++ [last_key]))
              (round_spec Nr is_decrypt init_key init_state 0) =
    if is_decrypt
    then
      Cipher.equivalent_inverse_cipher
        _ _ add_round_key_spec inv_sub_bytes_spec inv_shift_rows_spec
        inv_mix_columns_spec init_key last_key
        (map inv_mix_columns_spec middle_keys) init_state
    else
      Cipher.cipher _ _ add_round_key_spec sub_bytes_spec shift_rows_spec
                    mix_columns_spec init_key last_key middle_keys init_state.
  Proof.
    intros. rewrite <-seq_shift, combine_map_l.
    rewrite fold_left_map. destruct Nr; [ Lia.lia | ].
    autorewrite with pull_snoc.
    rewrite combine_append by length_hammer.
    cbn [combine]. autorewrite with pull_snoc natsimpl.
    cbn [fst snd].
    cbv [equivalent_inverse_cipher Cipher.cipher].
    rewrite fold_left_to_seq with (default:=(0,init_key)).
    rewrite !fold_left_to_seq with (default:=init_key).
    autorewrite with push_length natsimpl.
    replace (length middle_keys) with Nr by Lia.lia.
    destruct is_decrypt.
    { cbv [round_spec]. repeat destruct_one_match; try Lia.lia; [ ].
      factor_out_loops.
      eapply fold_left_double_invariant_seq with
          (I:=fun _ st1 st2 => st1 = st2);
        [ reflexivity | | congruence ].
      intros; subst.
      autorewrite with push_nth natsimpl. cbn [fst snd].
      rewrite map_nth_inbounds with (d2:=init_key) by length_hammer.
      repeat destruct_one_match; try Lia.lia. reflexivity. }
    { cbv [round_spec]. repeat destruct_one_match; try Lia.lia; [ ].
      factor_out_loops.
      eapply fold_left_double_invariant_seq with
          (I:=fun _ st1 st2 => st1 = st2);
        [ reflexivity | | congruence ].
      intros; subst.
      autorewrite with push_nth natsimpl. cbn [fst snd].
      repeat destruct_one_match; try Lia.lia. reflexivity. }
  Qed.

  Lemma cipher_equiv
        (key_expand : Circuit _ _)
        (Nr : nat) init_state_ignored
        (is_decrypt : bool)
        (init_key : key) (init_state : state)
        (last_key : key) (middle_keys : list key)
        (cipher_input : list _) :(* Nr must be at least two and small enough to fit in round_index size *)
    1 < Nr < 2 ^ 4 ->
    length init_state_ignored = Nr ->
    length middle_keys = Nr - 1 ->
    cipher_input = make_cipher_signals Nr is_decrypt
                                       (init_state :: init_state_ignored) ->
    (* precomputed keys match key expansion *)
    multistep key_expand cipher_input = init_key :: middle_keys ++ [last_key] ->
    let cipher := cipher
                    (key:=Vec (Vec (Vec Bit 8) 4) 4)
                    (state:=Vec (Vec (Vec Bit 8) 4) 4)
                    (round_index:=Vec Bit 4)
                    sub_bytes shift_rows mix_columns add_round_key (mix_columns true)
                    key_expand in
    forall d,
      nth Nr (multistep cipher cipher_input) d
      = if is_decrypt
        then
          Cipher.equivalent_inverse_cipher
            _ _ add_round_key_spec inv_sub_bytes_spec inv_shift_rows_spec
            inv_mix_columns_spec init_key last_key
            (map inv_mix_columns_spec middle_keys) init_state
        else
          Cipher.cipher
            _ _ add_round_key_spec sub_bytes_spec shift_rows_spec
            mix_columns_spec init_key last_key middle_keys init_state.
  Proof.
    cbv zeta; intros. subst cipher_input.
    cbv [cipher]. autorewrite with push_multistep.
    rewrite !map_map.
    rewrite !ListUtils.map_id_ext by reflexivity.
    erewrite cipher_loop_equiv with (Nr:=Nr) (init_state_ignored:=init_state_ignored)
      by length_hammer.
    match goal with Hkexp : multistep key_expand _ = _ |- _ =>
                    cbv [combType Bvector.Bvector] in Hkexp |- *;
                      rewrite Hkexp; clear Hkexp end.
    cbv [cipher_trace_with_keys]. simplify.

    cbn [seq combine]. rewrite fold_left_accumulate_cons.
    cbn [tl]. rewrite nth_fold_left_accumulate by length_hammer.
    rewrite !firstn_all2 by length_hammer.

    erewrite <-fold_round_spec_equiv with (Nr:=Nr) by length_hammer.
    reflexivity.
  Qed.
End WithSubroutines.
