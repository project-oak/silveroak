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

Require Import Coq.NArith.NArith.
Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.Semantics.
Local Open Scope N_scope.

Require Import Coq.micromega.Lia.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Tactics.
Require Import Cava.ExprProperties.

Module N.
  Lemma mod_mod_mul_l a b c : b <> 0 -> c <> 0 -> (a mod (b * c)) mod c = a mod c.
  Proof.
    intros. rewrite (N.mul_comm b c).
    rewrite N.mod_mul_r, N.add_mod, N.mod_mul_l, N.add_0_r by lia.
    rewrite !N.mod_mod by lia. reflexivity.
  Qed.
  Lemma div_floor a b : b <> 0 -> (a - a mod b) / b = a / b.
  Proof.
    intros. rewrite (N.div_mod a b) at 1 by lia.
    rewrite N.add_sub, N.div_mul_l; lia.
  Qed.
  Lemma mod_mul_div_r a b c :
    b <> 0 -> c <> 0 -> a mod (b * c) / c = (a / c) mod b.
  Proof.
    intros.
    rewrite (N.mul_comm b c), N.mod_mul_r by lia.
    rewrite (N.mul_comm c (_ mod b)), N.div_add by lia.
    rewrite (N.div_small (_ mod c) c) by (apply N.mod_bound_pos; lia).
    lia.
  Qed.
End N.

(**** Example using invariant logic ****)
Module Example.
  Section CircuitDefinitions.
    Context {var : tvar}.
    Import ExprNotations.
    Import PrimitiveNotations.

    (* Circuit which takes a bit indicating whether to increment or not, and if
       the bit is true increments an n-bit counter by 1 each cycle. The counter
       truncates on overflow and returns the counter value along with a bit
       indicating whether the counter overflowed. *)
    Definition counter (n : nat) : Circuit (BitVec n ** Bit) [Bit] (BitVec n ** Bit) :=
      {{ fun enable =>
           let/delay '(data; overflow) :=
              (if !enable
               then (data,`Zero`)
               else
                 let new_overflow := data == `K (N.ones (N.of_nat n))` in
                 let new_data := data + `K 1` in
                 (new_data, new_overflow))
                initially
                ((0,false) : denote_type (BitVec n ** Bit)) in
           (data,overflow)
      }}.

    (* Creates a 2n-bit counter out of two n-bit counters *)
    Definition double_counter (n : nat) : Circuit _ [Bit] (BitVec (2 * n) ** Bit) :=
      {{ fun enable =>
           let '(low; low_overflow) := `counter n` enable in
           let '(high; high_overflow) := `counter n` low_overflow in
           (`bvresize _` (`bvconcat` high low), high_overflow) }}.
  End CircuitDefinitions.

  Section Specifications.
    (* Ghost state : counter value *)
    Definition counter_ghost_state : Type := N.

    (* Invariant: the counter value must be < 2 ^ n. *)
    Definition counter_invariant {n}
               (state : denote_type (state_of (var:=denote_type) (counter n)))
               (* Ghost variable tracking counter value *)
               (ghost_state : counter_ghost_state)
    : Prop :=
      let '(data, _) := state in
      let value := ghost_state in
      (* value is exactly equivalent to [data] *)
      data = value
      (* ...and value < 2 ^ n *)
      /\ (value < 2 ^ N.of_nat n)%N.

    (* No input preconditions *)
    Definition counter_pre {n}
               (input : denote_type (input_of (var:=denote_type) (counter n)))
               (ghost_state : counter_ghost_state)
      : Prop := True.

    Definition counter_spec {n}
               (input : denote_type (input_of (var:=denote_type) (counter n)))
               (ghost_state : counter_ghost_state)
      : denote_type (output_of (var:=denote_type) (counter n)) :=
      let '(enable,_) := input in
      let value := ghost_state in
      let new_val := if enable then (value + 1)%N else value in
      (new_val mod (2 ^ N.of_nat n), (2 ^ N.of_nat n <=? new_val))%N.

    Definition counter_update_ghost_state {n}
               (input : denote_type (input_of (counter (var:=denote_type) n)))
               (ghost_state : counter_ghost_state) : counter_ghost_state :=
      let '(enable,_) := input in
      let value := ghost_state in
      if enable
      then ((value + 1) mod (2 ^ N.of_nat n))%N
      else value.

    (* Double counter ghost state is also just a value *)
    Definition double_counter_ghost_state := counter_ghost_state.

    Definition double_counter_invariant {n}
               (state : denote_type (state_of (double_counter (var:=denote_type) n)))
               (* Ghost variable tracking double_counter value *)
               (ghost_state : double_counter_ghost_state)
    : Prop :=
      let '(counter1_state, counter2_state) := state in
      let value := ghost_state in
      (* counter1_state matches the low part of the counter value *)
      counter_invariant (n:=n) counter1_state (value mod 2 ^ N.of_nat n)%N
      (* ...and counter2_state matches the high part of the counter value *)
      /\ counter_invariant (n:=n) counter2_state (value / 2 ^ N.of_nat n)%N
      (* ...and the value is < 2 ^ 2n (this is implied by the other two but
         convenient to have without unfolding [counter_invariant]) *)
      /\ value < 2 ^ (N.of_nat (2 * n)).

    (* No input preconditions *)
    Definition double_counter_pre {n}
               (input : denote_type (input_of (double_counter (var:=denote_type) n)))
               (ghost_state : double_counter_ghost_state)
      : Prop := True.

    (* Spec is the same as a double-size counter *)
    Definition double_counter_spec {n}
               (input : denote_type (input_of (double_counter (var:=denote_type) n)))
               (ghost_state : double_counter_ghost_state)
      : denote_type (output_of (double_counter (var:=denote_type) n)) :=
      counter_spec (n:=2*n) input ghost_state.

    Definition double_counter_update_ghost_state {n}
               (input : denote_type (input_of (double_counter (var:=denote_type) n)))
               (ghost_state : double_counter_ghost_state) : double_counter_ghost_state :=
      counter_update_ghost_state (n:=2*n) input ghost_state.
  End Specifications.

  Section Proofs.


    (* TODO: move *)
    Lemma step_bvresize {n m} (x : denote_type (BitVec n)) :
      step (bvresize (n:=n) m) tt (x, tt) = (tt, N.land x (N.ones (N.of_nat m))).
    Proof. reflexivity. Qed.
    Hint Rewrite @step_bvresize using solve [eauto] : stepsimpl.
    (* TODO: move *)
    Lemma step_bvconcat {n m} (x : denote_type (BitVec n)) (y : denote_type (BitVec m)) :
      step (bvconcat (n:=n) (m:=m)) tt (x, (y, tt))
      = (tt, N.lor (N.shiftl (N.land x (N.ones (N.of_nat n))) (N.of_nat m))
                   (N.land y (N.ones (N.of_nat (n + m))))).
    Proof.
      cbv [bvconcat]. stepsimpl. f_equal.
      apply N.bits_inj; intro i. push_Ntestbit.
      rewrite Nat2N.inj_add.
      destruct_one_match; push_Ntestbit; boolsimpl; [ | reflexivity ].
      destr (i <? N.of_nat m)%N; push_Ntestbit; boolsimpl; reflexivity.
    Qed.
    Hint Rewrite @step_bvconcat using solve [eauto] : stepsimpl.

    Lemma step_counter_invariant n state ghost_state new_ghost_state input :
      counter_invariant (n:=n) state ghost_state ->
      counter_pre (n:=n) input ghost_state ->
      new_ghost_state = counter_update_ghost_state input ghost_state ->
      counter_invariant (fst (step (counter n) state input))
                        new_ghost_state.
    Admitted.

    Lemma step_counter n state ghost_state input :
      counter_invariant (n:=n) state ghost_state ->
      counter_pre (n:=n) input ghost_state ->
      snd (step (counter n) state input)
      = counter_spec input ghost_state.
    Admitted.

    Lemma step_double_counter_invariant n state ghost_state new_ghost_state input :
      double_counter_invariant (n:=n) state ghost_state ->
      double_counter_pre (n:=n) input ghost_state ->
      new_ghost_state = double_counter_update_ghost_state input ghost_state ->
      double_counter_invariant (fst (step (double_counter n) state input))
                               new_ghost_state.
    Proof.
      destruct state as (data, ?). rename ghost_state into value.
      destruct input as (enable,[]).
      cbv [double_counter_invariant double_counter_pre]; intros; subst.
      cbv [double_counter]. stepsimpl.
      logical_simplify; subst. natsimpl.
      lazymatch goal with
      | |- context [match step (counter ?n) ?s ?i with pair _ _ => _ end] =>
        rewrite (surjective_pairing (step (counter n) s i))
      end.
      erewrite step_counter by eauto.
      cbv [counter_spec].
      stepsimpl.
      lazymatch goal with
      | |- context [match step (counter ?n) ?s ?i with pair _ _ => _ end] =>
        rewrite (surjective_pairing (step (counter n) s i))
      end.
      erewrite step_counter by eauto.
      cbv [counter_spec].
      stepsimpl.
      (* helpful assertions *)
      assert (2 ^ N.of_nat n <> 0) by (apply N.pow_nonzero; lia).
      pose proof N.mod_bound_pos value (2 ^ N.of_nat n) ltac:(lia) ltac:(lia).
      cbv [double_counter_update_ghost_state counter_update_ghost_state].
      ssplit.
      { eapply step_counter_invariant; [ solve [eauto] .. | ].
        cbv [counter_update_ghost_state].
        destruct enable; [ | reflexivity ].
        rewrite N.add_mod_idemp_l, Nat2N.inj_mul by lia.
        replace (N.of_nat 2 * N.of_nat n) with (N.of_nat n * 2) by lia.
        rewrite N.pow_mul_r, N.pow_2_r.
        rewrite N.mod_mod_mul_l by lia.
        reflexivity. }
      { eapply step_counter_invariant; [ solve [eauto] .. | ].
        cbv [counter_update_ghost_state].
        repeat (destruct_one_match; try lia).
        { (* this is the case in which the low counter overflows -- adding 1 and
             then taking the high part is therefore the same as taking the high
             part and adding 1 *)
          replace (N.of_nat (2 * n)) with (N.of_nat n * 2) by lia.
          rewrite N.pow_mul_r, N.pow_2_r by lia.
          rewrite N.mod_mul_div_r by lia.
          (* remember high part so as not to change it with the N.div_mod rewrite *)
          remember (value / 2 ^ N.of_nat n) as X.
          rewrite (N.div_mod value (2 ^ N.of_nat n)) by lia.
          subst X.
          lazymatch goal with
          | H : ?x <= ?y mod ?x + 1 |- _ =>
            replace (y mod x) with (x - 1) in * by lia
          | _ => idtac
          end.
          lazymatch goal with
          | |- context [?x + (?y - ?z) + ?z] =>
            replace (x + (y - z) + z) with (x + y) by lia
          end.
          rewrite (N.mul_comm (2 ^ N.of_nat n) (_ / _)).
          rewrite N.div_add_l, N.div_same by lia.
          reflexivity. }
        { (* more ugly modular-arithmetic reasoning *)
          replace (N.of_nat (2 * n)) with (N.of_nat n * 2) in * by lia.
          rewrite N.pow_mul_r, N.pow_2_r in * by lia.
          rewrite N.mod_mul_div_r by lia.
          rewrite (N.div_mod value (2 ^ N.of_nat n)) at 1 by lia.
          rewrite (N.mul_comm (2 ^ _) (_ / _)), <-N.add_assoc.
          rewrite N.div_add_l by lia.
          rewrite (N.div_small (_ + 1) _), N.add_0_r by lia.
          apply N.mod_small, N.div_lt_upper_bound; lia. } }
      { destruct enable; [ | lia ].
        apply N.mod_bound_pos; lia. }
    Qed.

    Lemma step_double_counter n state ghost_state input :
      double_counter_invariant (n:=n) state ghost_state ->
      double_counter_pre (n:=n) input ghost_state ->
      snd (step (double_counter n) state input)
      = double_counter_spec input ghost_state.
    Proof.
      destruct state as (data, ?). rename ghost_state into value.
      destruct input as (enable,[]).
      cbv [double_counter_invariant double_counter_pre]; intros; subst.
      cbv [double_counter double_counter_spec]. stepsimpl.
      logical_simplify; subst. natsimpl.
      lazymatch goal with
      | |- context [match step (counter ?n) ?s ?i with pair _ _ => _ end] =>
        rewrite (surjective_pairing (step (counter n) s i))
      end.
      erewrite step_counter by eauto.
      cbv [counter_spec].
      stepsimpl.
      lazymatch goal with
      | |- context [match step (counter ?n) ?s ?i with pair _ _ => _ end] =>
        rewrite (surjective_pairing (step (counter n) s i))
      end.
      erewrite step_counter by eauto.
      cbv [counter_spec].
      stepsimpl.
      f_equal.
      { (* counter values match *)
        (* TODO: consider making moduli constants so that nice automation works *)
        rewrite <-!N.shiftr_div_pow2.
        rewrite <-!N.land_ones.
        destr enable.
    Qed.
  End Proofs.
End Example.




