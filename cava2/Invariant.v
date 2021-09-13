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

Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.Semantics.
Local Open Scope N_scope.

Require Import Coq.micromega.Lia.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Util.List.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Tactics.
Require Import Cava.ExprProperties.

Class invariant_logic_for {s i o} (c : Circuit (var:=denote_type) s i o)
      (hl_state : Type) :=
  { reset_hl_state : hl_state;
    update_hl_state : denote_type i -> hl_state -> hl_state;
    invariant_for : denote_type s -> hl_state -> Prop;
    precondition_for : denote_type i -> hl_state -> Prop;
    spec_for : denote_type i -> hl_state -> denote_type o;
  }.
Global Arguments invariant_for {_ _ _} _ {_ _}.
Global Arguments precondition_for {_ _ _} _ {_ _}.
Global Arguments spec_for {_ _ _} _ {_ _}.

Definition invariant_at_reset {s i o} (c : Circuit s i o)
           {hl_state} {invariant_logic : invariant_logic_for c hl_state} : Prop :=
  invariant_for c (reset_state c) reset_hl_state.
Existing Class invariant_at_reset.

Definition invariant_preserved {s i o} (c : Circuit s i o)
           {hl_state} {invariant_logic : invariant_logic_for c hl_state} : Prop :=
  forall input state hl_state new_hl_state,
    new_hl_state = update_hl_state input hl_state ->
    invariant_for c state hl_state ->
    precondition_for c input hl_state ->
    invariant_for c (fst (step c state input)) new_hl_state.
Existing Class invariant_preserved.

Definition output_correct {s i o} (c : Circuit s i o)
           {hl_state} {invariant_logic : invariant_logic_for c hl_state} : Prop :=
  forall input state hl_state,
    invariant_for c state hl_state ->
    precondition_for c input hl_state ->
    snd (step c state input) = spec_for c input hl_state.
Existing Class output_correct.

Class correctness_for {s i o} (c : Circuit s i o)
      {hl_state} {invariant_logic : invariant_logic_for c hl_state} :=
  { invariant_at_reset_pf : invariant_at_reset c;
    invariant_preserved_pf : invariant_preserved c;
    output_correct_pf : output_correct c }.

(* Succeeds if an instance is found for circuit correctness *)
Ltac find_correctness c :=
  let x := constr:(_:correctness_for c) in
  idtac.

Ltac simplify_invariant_logic c :=
  let x := constr:(_:invariant_logic_for c _) in
  match x with
  | ?x => cbn [x update_hl_state invariant_for precondition_for
                spec_for invariant_at_reset invariant_preserved
                output_correct reset_hl_state] in *
  end.
Ltac simplify_spec c :=
  let x := constr:(_:invariant_logic_for c _) in
  match x with
  | ?x => cbn [spec_for x] in *
  end.

(* if a subcircuit is found that has an invariant-based correctness proof, use
   the correctness proof to replace the circuit step function with the
   spec. Uses [eauto] to solve the side conditions of the output-correctness
   proof. *)
Ltac use_correctness :=
  match goal with
  | |- context [match step ?c ?s ?i with pair _ _ => _ end] =>
    find_correctness c;
    rewrite (surjective_pairing (step c s i));
    erewrite (output_correct_pf (c:=c)) by eauto;
    simplify_spec c
  end.

Section StateLogicProofs.
  Context {s i o} (c : Circuit (var:=denote_type) s i o).
  Context {hl_state} {invariant_logic : invariant_logic_for c hl_state}.
  Context {correctness : correctness_for c}.

  Lemma simulate_invariant_logic input :
    (* TODO: refine this. The precondition has to hold at each step; for now,
       just say that each of the inputs satisfies the precondition for all
       states *)
    Forall (fun i => forall s, precondition_for c i s) input ->
    simulate c input = fold_left_accumulate
                         (fun s i => (update_hl_state i s, spec_for _ i s))
                         input reset_hl_state.
  Proof.
    intros.
    change (simulate c input) with
        (fold_left_accumulate (step c) input (reset_state c)).
    eapply fold_left_accumulate_double_invariant_In
      with (I:=fun s1 s2 acc1 acc2 =>
                 invariant_for c s1 s2 /\ acc1 = acc2).
    { ssplit; [ | reflexivity ].
      apply invariant_at_reset_pf. }
    { intros; logical_simplify; subst.
      pose proof (proj1 (Forall_forall _ _))
           ltac:(eassumption) _ ltac:(eassumption).
      cbv beta in *.
      ssplit.
      { eapply invariant_preserved_pf; [ | solve [eauto] .. ].
        reflexivity. }
      { rewrite output_correct_pf; [ | solve [eauto] .. ].
        reflexivity. } }
    { intros; logical_simplify; subst. reflexivity. }
  Qed.
End StateLogicProofs.


(**** Example usage of invariant logic ****)
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

    Global Instance counter_invariant_logic
      : invariant_logic_for counter N :=
      {| reset_hl_state := 0;
         update_hl_state :=
           fun (input : denote_type [Bit]) value =>
             let '(enable,_) := input in
             (* if enabled, add 1 mod 2^8, else do nothing *)
             if enable
             then ((value + 1) mod (2 ^ 8))%N
             else value;
         invariant_for :=
           fun (state : denote_type (BitVec 8 ** _)) value =>
             let '(data,_) := state in
             (* value is exactly equivalent to [data] *)
             data = value
             (* ...and value < 2 ^ 8 *)
             /\ value < 2 ^ 8;
         precondition_for := fun _ _ => True;
         spec_for :=
           fun input value =>
             let '(enable,_) := input in
             let new_val := if enable then (value + 1)%N else value in
             ((new_val mod (2 ^ 8), 2 ^ 8 <=? new_val)
              : denote_type (BitVec 8 ** Bit))
      |}.

    Global Instance double_counter_invariant_logic
      : invariant_logic_for double_counter N :=
      {| reset_hl_state := 0;
         update_hl_state :=
           fun (input : denote_type [Bit]) value =>
             let '(enable,_) := input in
             (* if enabled, add 1 mod 2^16, else do nothing *)
             if enable
             then ((value + 1) mod (2 ^ 16))%N
             else value;
         invariant_for :=
           fun (state : denote_type (state_of (var:=denote_type) counter
                                            ** state_of (var:=denote_type) counter)) value =>
             let '(counter1_state, counter2_state) := state in
             (* counter1_state matches the low part of the counter value *)
             invariant_for counter counter1_state (value mod 2 ^ 8)%N
             (* ...and counter2_state matches the high part of the counter value *)
             /\ invariant_for counter counter2_state (value / 2 ^ 8)%N
             (* ...and the value is < 2 ^ 16 (this is implied by the other two but
                convenient to have without unfolding [counter_invariant]) *)
             /\ value < 2 ^ 16;
         precondition_for := fun _ _ => True;
         spec_for :=
           fun input value =>
             let '(enable,_) := input in
             let new_val := if enable then (value + 1)%N else value in
             ((new_val mod (2 ^ 16), 2 ^ 16 <=? new_val)
              : denote_type (BitVec 16 ** Bit))
      |}.
  End Specifications.

  Section Proofs.
    Lemma counter_invariant_at_reset : invariant_at_reset counter.
    Proof.
      simplify_invariant_logic counter.
      cbv [counter]. cbn [reset_state]. stepsimpl.
      ssplit; [ reflexivity | ]. cbn; lia.
    Qed.

    Lemma counter_invariant_preserved : invariant_preserved counter.
    Proof.
      intros (enable,[]) (data, ?) value. intros; subst.
      simplify_invariant_logic counter.
      cbv [counter]. stepsimpl. logical_simplify; subst.
      destruct enable; cbn [negb fst snd].
      all:ssplit; first [ lia | reflexivity
                        | apply N.mod_bound_pos; lia ].
    Qed.

    Lemma counter_output_correct : output_correct counter.
    Proof.
      intros (enable,[]) (data, ?) value.
      simplify_invariant_logic counter.
      intros; logical_simplify; subst.
      cbv [counter]. stepsimpl. compute_expr (N.of_nat 8).
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

    Existing Instances counter_invariant_at_reset counter_invariant_preserved
             counter_output_correct.
    Global Instance counter_correctness : correctness_for counter.
    Proof. constructor; typeclasses eauto. Defined.

    Lemma double_counter_invariant_at_reset : invariant_at_reset double_counter.
    Proof.
      simplify_invariant_logic double_counter.
      cbn [double_counter reset_state].
      stepsimpl. rewrite N.mod_0_l, N.div_0_l by (cbn; lia).
      ssplit; [ eapply counter_invariant_at_reset .. | ].
      cbn; lia.
    Qed.

    Lemma double_counter_invariant_preserved : invariant_preserved double_counter.
    Proof.
      cbv [invariant_preserved]. intros (enable,[]) (data,?) value.
      intros; subst. simplify_invariant_logic double_counter.
      cbv [double_counter]. stepsimpl. logical_simplify; subst.
      repeat use_correctness. stepsimpl.
      ssplit.
      { eapply (invariant_preserved_pf (c:=counter));
          [ | solve [eauto] .. ].
        cbn [update_hl_state counter_invariant_logic].
        destruct enable; [ | reflexivity ].
        change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in *.
        Zify.zify. Z.to_euclidean_division_equations. lia. }
      {eapply (invariant_preserved_pf (c:=counter));
          [ | solve [eauto] .. ].
        cbn [update_hl_state counter_invariant_logic].
        change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in *.
        repeat (destruct_one_match; try lia).
        (* extra step to help lia out, otherwise hangs *)
        all:try rewrite N.mod_mul_div_r with (b:=256) (c:=256) by lia.
        all:Zify.zify; Z.to_euclidean_division_equations; lia. }
      { destruct enable; [ | lia ].
        apply N.mod_bound_pos; lia. }
    Qed.

    Lemma double_counter_output_correct : output_correct double_counter.
    Proof.
      cbv [output_correct]. intros (enable,[]) (data, ?) value.
      simplify_invariant_logic double_counter.
      intros; logical_simplify; subst.
      cbv [double_counter]. stepsimpl.
      repeat use_correctness. stepsimpl.
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

    Existing Instances double_counter_invariant_at_reset double_counter_invariant_preserved
             double_counter_output_correct.
    Global Instance double_counter_correctness : correctness_for double_counter.
    Proof. constructor; typeclasses eauto. Defined.
  End Proofs.
End Example.
