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
Require Import Coq.ZArith.ZArith.
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
  Lemma lor_high_low_add a b c :
    N.lor (a * 2 ^ b) (c mod 2 ^ b) = a * 2 ^ b + c mod 2 ^ b.
  Proof.
    rewrite <-!N.shiftl_mul_pow2, <-!N.land_ones.
    apply N.bits_inj; intro i. push_Ntestbit.
    pose proof N.mod_pow2_bits_full (a * 2 ^ b + c mod 2 ^ b) b i as Hlow.
    rewrite N.add_mod, N.mod_mul, N.add_0_l, !N.mod_mod in Hlow
      by (apply N.pow_nonzero; lia).
    rewrite <-!N.shiftl_mul_pow2, <-!N.land_ones in Hlow.
    (* helpful assertion *)
    assert (2 ^ b <> 0) by (apply N.pow_nonzero; lia).
    destr (i <? b).
    { rewrite <-Hlow. push_Ntestbit. boolsimpl. reflexivity. }
    {  autorewrite with push_Ntestbit in  Hlow. rewrite Hlow.
       push_Ntestbit; boolsimpl.
       replace i with (i - b + b) by lia.
       rewrite N.add_sub. rewrite <-N.div_pow2_bits.
       rewrite N.shiftl_mul_pow2, N.land_ones.
       rewrite N.div_add_l by lia.
       rewrite N.div_small by (apply N.mod_bound_pos; lia).
       f_equal; lia. }
  Qed.

End N.

(**** Example using invariant logic ****)
Module Example.
  Section CircuitDefinitions.
    Context {var : tvar}.
    Import ExprNotations.
    Import PrimitiveNotations.

    (* Circuit which takes a bit indicating whether to increment or not, and if
       the bit is true increments an 8-bit counter by 1 each cycle. The counter
       truncates on overflow and returns the counter value along with a bit
       indicating whether the counter overflowed. *)
    Definition counter : Circuit (BitVec 8 ** Bit) [Bit] (BitVec 8 ** Bit) :=
      {{ fun enable =>
           let/delay '(data; overflow) :=
              (if !enable
               then (data,`Zero`)
               else
                 let new_overflow := data == `K (N.ones 8)` in
                 let new_data := data + `K 1` in
                 (new_data, new_overflow))
                initially
                ((0,false) : denote_type (BitVec 8 ** Bit)) in
           (data,overflow)
      }}.

    (* Creates a 16-bit counter out of two 8-bit counters *)
    Definition double_counter : Circuit _ [Bit] (BitVec 16 ** Bit) :=
      {{ fun enable =>
           let '(low; low_overflow) := `counter` enable in
           let '(high; high_overflow) := `counter` low_overflow in
           (`bvresize 16` (`bvconcat` high low), high_overflow) }}.
  End CircuitDefinitions.

  Section Specifications.
    (* Ghost state : counter value *)
    Definition counter_hl_state : Type := N.

    (* Invariant: the counter value must be < 2 ^ 8. *)
    Definition counter_invariant
               (state : denote_type (state_of (var:=denote_type) counter))
               (* Ghost variable tracking counter value *)
               (hl_state : counter_hl_state)
    : Prop :=
      let '(data, _) := state in
      let value := hl_state in
      (* value is exactly equivalent to [data] *)
      data = value
      (* ...and value < 2 ^ 8 *)
      /\ value < 2 ^ 8.

    (* No input preconditions *)
    Definition counter_pre
               (input : denote_type (input_of (var:=denote_type) counter))
               (hl_state : counter_hl_state)
      : Prop := True.

    Definition counter_spec
               (input : denote_type (input_of (var:=denote_type) counter))
               (hl_state : counter_hl_state)
      : denote_type (output_of (var:=denote_type) counter) :=
      let '(enable,_) := input in
      let value := hl_state in
      let new_val := if enable then (value + 1)%N else value in
      (new_val mod (2 ^ 8), 2 ^ 8 <=? new_val).

    Definition counter_update_hl_state
               (input : denote_type (input_of (counter (var:=denote_type))))
               (hl_state : counter_hl_state) : counter_hl_state :=
      let '(enable,_) := input in
      let value := hl_state in
      if enable
      then ((value + 1) mod (2 ^ 8))%N
      else value.

    (* Double counter high-level state is also just a value *)
    Definition double_counter_hl_state := counter_hl_state.

    Definition double_counter_invariant
               (state : denote_type (state_of (double_counter (var:=denote_type))))
               (* High-level state variable tracking double_counter value *)
               (hl_state : double_counter_hl_state)
    : Prop :=
      let '(counter1_state, counter2_state) := state in
      let value := hl_state in
      (* counter1_state matches the low part of the counter value *)
      counter_invariant counter1_state (value mod 2 ^ 8)%N
      (* ...and counter2_state matches the high part of the counter value *)
      /\ counter_invariant counter2_state (value / 2 ^ 8)%N
      (* ...and the value is < 2 ^ 16 (this is implied by the other two but
         convenient to have without unfolding [counter_invariant]) *)
      /\ value < 2 ^ 16.

    (* No input preconditions *)
    Definition double_counter_pre
               (input : denote_type (input_of (double_counter (var:=denote_type))))
               (hl_state : double_counter_hl_state)
      : Prop := True.

    (* Spec is the same as a double-size counter *)
    Definition double_counter_spec
               (input : denote_type (input_of (double_counter (var:=denote_type))))
               (hl_state : double_counter_hl_state)
      : denote_type (output_of (double_counter (var:=denote_type))) :=
      let '(enable,_) := input in
      let value := hl_state in
      let new_val := if enable then (value + 1)%N else value in
      (new_val mod (2 ^ 16), 2 ^ 16 <=? new_val).

    Definition double_counter_update_hl_state
               (input : denote_type (input_of (double_counter (var:=denote_type))))
               (hl_state : double_counter_hl_state) : double_counter_hl_state :=
      let '(enable,_) := input in
      let value := hl_state in
      if enable
      then ((value + 1) mod (2 ^ 16))%N
      else value.
  End Specifications.

  Section Proofs.

    Lemma step_counter_invariant state hl_state new_hl_state input :
      counter_invariant state hl_state ->
      counter_pre input hl_state ->
      new_hl_state = counter_update_hl_state input hl_state ->
      counter_invariant (fst (step counter state input))
                        new_hl_state.
    Proof.
      destruct state as (data, ?). rename hl_state into value.
      destruct input as (enable,[]).
      cbv [counter_invariant counter_pre]; intros; subst.
      cbv [counter]. stepsimpl. logical_simplify; subst.
      cbv [counter_update_hl_state].
      destruct enable; cbn [negb fst snd].
      all:ssplit; first [ lia
                        | reflexivity
                        | apply N.mod_bound_pos; lia ].
    Qed.

    Lemma step_counter state hl_state input :
      counter_invariant state hl_state ->
      counter_pre input hl_state ->
      snd (step counter state input)
      = counter_spec input hl_state.
    Proof.
      destruct state as (data, ?). rename hl_state into value.
      destruct input as (enable,[]).
      cbv [counter_invariant counter_pre]; intros; subst.
      cbv [counter]. stepsimpl. logical_simplify; subst.
      cbv [counter_spec]. compute_expr (N.of_nat 8).
      change (2 ^ 8) with 256 in *.
      change (N.ones 8) with 255 in *.
      destruct enable; cbn [negb fst snd].
      all:repeat lazymatch goal with
                 | |- context [N.eqb ?x ?y] => destr (N.eqb x y); subst
                 | |- context [N.leb ?x ?y] => destr (N.leb x y)
                 | _ => lia || reflexivity
                 end.
      all:rewrite N.mod_small by lia; reflexivity.
    Qed.

    Lemma step_double_counter_invariant state hl_state new_hl_state input :
      double_counter_invariant state hl_state ->
      double_counter_pre input hl_state ->
      new_hl_state = double_counter_update_hl_state input hl_state ->
      double_counter_invariant (fst (step double_counter state input))
                               new_hl_state.
    Proof.
      destruct state as (data, ?). rename hl_state into value.
      destruct input as (enable,[]).
      cbv [double_counter_invariant double_counter_pre]; intros; subst.
      cbv [double_counter]. stepsimpl.
      logical_simplify; subst. natsimpl.
      lazymatch goal with
      | |- context [match step counter ?s ?i with pair _ _ => _ end] =>
        rewrite (surjective_pairing (step counter s i))
      end.
      erewrite !step_counter by eauto.
      cbv [counter_spec]. stepsimpl.
      lazymatch goal with
      | |- context [match step counter ?s ?i with pair _ _ => _ end] =>
        rewrite (surjective_pairing (step counter s i))
      end.
      erewrite step_counter by eauto.
      cbv [counter_spec].
      stepsimpl.
      cbv [double_counter_update_hl_state counter_update_hl_state].
      ssplit.
      { eapply step_counter_invariant; [ solve [eauto] .. | ].
        cbv [counter_update_hl_state]. destruct enable; [ | reflexivity ].
        change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in *.
        Zify.zify. Z.to_euclidean_division_equations. lia. }
      { eapply step_counter_invariant; [ solve [eauto] .. | ].
        cbv [counter_update_hl_state].
        change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in *.
        repeat (destruct_one_match; try lia).
        (* extra step to help lia out, otherwise hangs *)
        all:try rewrite N.mod_mul_div_r with (b:=256) (c:=256) by lia.
        all:Zify.zify; Z.to_euclidean_division_equations; lia. }
      { destruct enable; [ | lia ].
        apply N.mod_bound_pos; lia. }
    Qed.

    Lemma step_double_counter state hl_state input :
      double_counter_invariant state hl_state ->
      double_counter_pre input hl_state ->
      snd (step double_counter state input)
      = double_counter_spec input hl_state.
    Proof.
      destruct state as (data, ?). rename hl_state into value.
      destruct input as (enable,[]).
      cbv [double_counter_invariant double_counter_pre]; intros; subst.
      cbv [double_counter double_counter_spec]. stepsimpl.
      logical_simplify; subst. natsimpl.
      lazymatch goal with
      | |- context [match step counter ?s ?i with pair _ _ => _ end] =>
        rewrite (surjective_pairing (step counter s i))
      end.
      erewrite step_counter by eauto.
      cbv [counter_spec].
      stepsimpl.
      lazymatch goal with
      | |- context [match step counter ?s ?i with pair _ _ => _ end] =>
        rewrite (surjective_pairing (step counter s i))
      end.
      erewrite step_counter by eauto.
      cbv [counter_spec].
      stepsimpl.
      f_equal.
      { (* counter values match *)
        compute_expr (N.of_nat 8). compute_expr (8 + 8)%nat.
        compute_expr (N.of_nat 16).
        rewrite !N.shiftl_mul_pow2, !N.land_ones.
        change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in *.
        rewrite !(N.mod_small (_ mod 256) 65536)
          by (eapply N.lt_le_trans; [ apply N.mod_bound_pos | ]; lia).
        rewrite N.lor_high_low_add with (b:=8). change (2 ^ 8) with 256 in *.
        repeat destruct_one_match.
        (* the below rewrite improves performance of lia *)
        all:rewrite ?N.mod_mod by lia.
        all:Zify.zify; Z.to_euclidean_division_equations; lia. }
      { change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in *.
        repeat destruct_one_match.
        all:repeat lazymatch goal with |- context [N.leb ?x ?y] =>
                                       destr (N.leb x y) end.
        all:try reflexivity.
        all:Zify.zify; Z.to_euclidean_division_equations; lia. }
    Qed.
  End Proofs.
End Example.




