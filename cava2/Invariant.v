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

Definition invariant_for {s i o} (c : Circuit (var:=denote_type) s i o)
           (repr : Type) : Type := denote_type s -> repr -> Prop.
Existing Class invariant_for.

Class specification_for {s i o} (c : Circuit (var:=denote_type) s i o)
      (repr : Type) :=
  { reset_repr : repr;
    update_repr : denote_type i -> repr -> repr;
    precondition : denote_type i -> repr -> Prop;
    postcondition : denote_type i -> repr -> denote_type o -> Prop;
  }.
Global Arguments precondition {_ _ _} _ {_ _}.
Global Arguments postcondition {_ _ _} _ {_ _}.

Definition invariant_at_reset {s i o} (c : Circuit s i o)
           {repr} {invariant : invariant_for c repr}
           {spec : specification_for c repr} : Prop :=
  invariant (reset_state c) reset_repr.
Existing Class invariant_at_reset.

Definition invariant_preserved {s i o} (c : Circuit s i o)
           {repr} {invariant : invariant_for c repr}
           {spec : specification_for c repr} : Prop :=
  forall input state r new_r,
    new_r = update_repr input r ->
    invariant state r ->
    precondition c input r ->
    invariant (fst (step c state input)) new_r.
Existing Class invariant_preserved.

Definition output_correct {s i o} (c : Circuit s i o)
           {repr} {invariant : invariant_for c repr}
           {spec : specification_for c repr} : Prop :=
  forall input state r,
    invariant state r ->
    precondition c input r ->
    postcondition c input r (snd (step c state input)).
Existing Class output_correct.

Class correctness_for {s i o} (c : Circuit s i o)
           {repr} {invariant : invariant_for c repr}
           {spec : specification_for c repr} : Prop :=
  { invariant_at_reset_pf : invariant_at_reset c;
    invariant_preserved_pf : invariant_preserved c;
    output_correct_pf : output_correct c }.

(* Switch between higher-level representations *)
Definition invariant_by_isomorphism {s i o} {c : Circuit s i o}
           {s1 s2} (phi : s1 -> s2) (inv : s2 -> s1)
           {invariant : invariant_for c s1}
  : invariant_for c s2 :=
  fun (state : denote_type s) x => invariant state (inv x).
Definition specification_by_isomorphism {s i o} {c : Circuit s i o}
           {s1 s2} (phi : s1 -> s2) (inv : s2 -> s1)
           {spec : specification_for c s1}
  : specification_for c s2 :=
  {| reset_repr := phi (reset_repr);
     update_repr := fun i x => phi (update_repr i (inv x));
     precondition := fun i x => precondition c i (inv x);
     postcondition := fun i x => postcondition c i (inv x);
  |}.

(* Succeeds if an instance is found for circuit correctness *)
Ltac find_correctness c :=
  let x := constr:(_:correctness_for c) in
  idtac.

Ltac simplify_invariant c :=
  cbv [invariant_at_reset invariant_preserved output_correct];
  let x := constr:(_:invariant_for c _) in
  match x with
  | ?x => cbv [x] in *
  | ?x _ => cbv [x] in *
  | ?x _ _ => cbv [x] in *
  | ?x _ _ _ => cbv [x] in *
  | ?x _ _ _ _ => cbv [x] in *
  | ?x _ _ _ _ _ => cbv [x] in *
  end.
Ltac simplify_spec c :=
  let x := constr:(_:specification_for c _) in
  match x with
  | ?x => cbn [x update_repr precondition postcondition] in *
  | ?x _ => cbn [x update_repr precondition postcondition] in *
  | ?x _ _ => cbn [x update_repr precondition postcondition] in *
  | ?x _ _ _ => cbn [x update_repr precondition postcondition] in *
  | ?x _ _ _ _ => cbn [x update_repr precondition postcondition] in *
  | ?x _ _ _ _ _ => cbn [x update_repr precondition postcondition] in *
  end.

(* if a subcircuit is found that has an invariant-based correctness proof, use
   the correctness proof to replace the circuit step function with the
   spec. Uses [eauto] to solve the side conditions of the output-correctness
   proof. *)
Ltac use_correctness' c :=
  lazymatch goal with
  | |- context [snd (step c ?s ?i)] =>
    find_correctness c;
    let H := fresh in
    pose proof (output_correct_pf (c:=c) i s _ ltac:(eauto) ltac:(eauto)) as H;
    cbn [absorb_any] in H;
    generalize dependent (snd (step c s i)); intros;
    try simplify_spec c; logical_simplify; subst
  end.
Ltac use_correctness :=
  match goal with
  | |- context [match step ?c ?s ?i with pair _ _ => _ end] =>
    find_correctness c;
    rewrite (surjective_pairing (step c s i));
    use_correctness' c
  end.

Section StateLogicProofs.
  Context {s i o} (c : Circuit (var:=denote_type) s i o).
  Context {repr} {invariant : invariant_for c repr}
          {spec : specification_for c repr}
          {correctness : correctness_for c}.

  Lemma simulate_invariant_logic input output_func :
    (* TODO: refine this. The precondition has to hold at each step; for now,
       just say that each of the inputs satisfies the precondition for all
       states *)
    Forall (fun i => forall s, precondition c i s) input ->
    (* the postcondition fully specifies the output *)
    (forall i s x, postcondition c i s x -> x = output_func i s) ->
    simulate c input = fold_left_accumulate
                         (fun s i => (update_repr i s, output_func i s))
                         input reset_repr.
  Proof.
    intros.
    change (simulate c input) with
        (fold_left_accumulate (step c) input (reset_state c)).
    eapply fold_left_accumulate_double_invariant_In
      with (I:=fun s1 s2 acc1 acc2 =>
                 invariant s1 s2 /\ acc1 = acc2).
    { ssplit; [ | reflexivity ].
      apply invariant_at_reset_pf. }
    { intros; logical_simplify; subst.
      pose proof (proj1 (Forall_forall _ _))
           ltac:(eassumption) _ ltac:(eassumption).
      cbv beta in *.
      ssplit.
      { eapply invariant_preserved_pf; [ | solve [eauto] .. ].
        reflexivity. }
      { use_correctness' c. cbn [fst snd].
        repeat (f_equal; eauto). } }
    { intros; logical_simplify; subst. reflexivity. }
  Qed.

  (* if there's an isomorphism between two higher-level states, then invariant
     logic and correctness proofs can be ported between them. *)
  Lemma invariant_logic_isomorphism_correct
        (repr' : Type) (phi : repr -> repr') (inv : repr' -> repr) :
    (forall x, inv (phi x) = x) ->
    correctness_for (invariant:=invariant_by_isomorphism phi inv)
                    (spec:=specification_by_isomorphism phi inv) c.
  Proof.
    intros Hphi.
    constructor; cbv [invariant_at_reset invariant_preserved output_correct
                                         specification_by_isomorphism
                                         invariant_by_isomorphism].
    all:cbn [reset_repr precondition postcondition].
    all:rewrite ?Hphi; intros; subst.
    all:eauto using invariant_preserved_pf, output_correct_pf.
    all:eapply invariant_at_reset_pf.
  Qed.
End StateLogicProofs.


(**** Example usage of invariant logic for counters ****)
Module DoubleCounterExample.
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

    Global Instance counter_specification
      : specification_for counter N :=
      {| reset_repr := 0;
         update_repr :=
           fun (input : denote_type [Bit]) value =>
             let '(enable,_) := input in
             (* if enabled, add 1 mod 2^n, else do nothing *)
             if enable
             then ((value + 1) mod (2 ^ 8))%N
             else value;
         precondition := fun _ _ => True;
         postcondition :=
           fun input value (output : denote_type (BitVec 8 ** Bit)) =>
             let '(enable,_) := input in
             let new_val := if enable then (value + 1)%N else value in
             output = (new_val mod (2 ^ 8), 2 ^ 8 <=? new_val)
      |}.

    Global Instance counter_invariant : invariant_for counter N :=
      fun (state : denote_type (BitVec 8 ** _)) value =>
        let '(data,_) := state in
        (* value is exactly equivalent to [data] *)
        data = value
        (* ...and value < 2 ^ 8 *)
        /\ value < 2 ^ 8.

    (* Almost identical to the counter specification *)
    Global Instance double_counter_specification
      : specification_for double_counter N :=
      {| reset_repr := 0;
         update_repr :=
           fun (input : denote_type [Bit]) value =>
             let '(enable,_) := input in
             (* if enabled, add 1 mod 2^n, else do nothing *)
             if enable
             then ((value + 1) mod (2 ^ 16))%N
             else value;
         precondition := fun _ _ => True;
         postcondition :=
           fun input value (output : denote_type (BitVec 16 ** Bit)) =>
             let '(enable,_) := input in
             let new_val := if enable then (value + 1)%N else value in
             output = (new_val mod (2 ^ 16), 2 ^ 16 <=? new_val)
      |}.

    Global Instance double_counter_invariant_logic
      : invariant_for double_counter N :=
      fun (state : denote_type (state_of counter
                                       ** state_of counter)) value =>
        let '(counter1_state, counter2_state) := state in
        (* counter1_state matches the low part of the counter value *)
        counter_invariant counter1_state (value mod 2 ^ 8)%N
        (* ...and counter2_state matches the high part of the counter value *)
        /\ counter_invariant counter2_state (value / 2 ^ 8)%N
        (* ...and the value is < 2 ^ 16 (this is implied by the other two but
           convenient to have without unfolding [counter_invariant]) *)
        /\ value < 2 ^ 16.
  End Specifications.

  Section Proofs.
    Lemma counter_invariant_at_reset : invariant_at_reset counter.
    Proof.
      simplify_invariant counter.
      cbv [counter]. cbn [reset_state]; stepsimpl.
      simplify_invariant counter.
      ssplit; [ reflexivity | ]. cbn; lia.
    Qed.

    Lemma counter_invariant_preserved : invariant_preserved counter.
    Proof.
      intros (enable,[]) (data, ?) value. intros; subst.
      simplify_invariant counter. simplify_spec counter.
      cbv [counter]. stepsimpl. logical_simplify; subst.
      destruct enable; cbn [negb fst snd].
      all:ssplit; first [ lia | reflexivity
                          | apply N.mod_bound_pos; lia ].
    Qed.

    Lemma counter_output_correct : output_correct counter.
    Proof.
      intros (enable,[]) (data, ?) value.
      simplify_invariant counter.
      intros; logical_simplify; subst.
      simplify_spec counter.
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
      simplify_invariant double_counter.
      cbn [double_counter reset_state].
      stepsimpl. rewrite N.mod_0_l, N.div_0_l by (cbn; lia).
      ssplit; [ eapply counter_invariant_at_reset .. | ].
      cbn; lia.
    Qed.

    Lemma double_counter_invariant_preserved : invariant_preserved double_counter.
    Proof.
      cbv [invariant_preserved]. intros (enable,[]) (data,?) value.
      intros; subst. simplify_invariant double_counter.
      cbv [double_counter]. stepsimpl. logical_simplify; subst.
      repeat use_correctness. stepsimpl.
      simplify_spec double_counter.
      ssplit.
      { eapply (invariant_preserved_pf (c:=counter));
          [ | solve [eauto] .. ].
        simplify_spec counter.
        destruct enable; [ | reflexivity ].
        change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in *.
        Zify.zify. Z.to_euclidean_division_equations. lia. }
      { eapply (invariant_preserved_pf (c:=counter));
        [ | solve [eauto] .. ].
        simplify_spec counter.
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
      simplify_invariant double_counter.
      simplify_spec double_counter.
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
End DoubleCounterExample.

(**** Example usage of invariant logic for circuit with abstract subcircuit ****)
Module AbstractSubcircuitExample.
  Section CircuitDefinitions.
    Context {var : tvar}.
    Import ExprNotations.
    Import PrimitiveNotations.

    (* Somewhat contrived circuit that takes in two streams of inputs of some
       type, and always returns the smallest input seen so far.

       * The [cmp] subcircuit retuns true if the first argument is <= the
         second, and false otherwise.
       * The [minimum] subcircuit has the same idea but with a single stream of
         inputs; its output is the smallest input seen so far.
     *)
    Definition double_minimum
               {T minimum_state} (cmp : Circuit [] [T;T] Bit)
               (minimum : Circuit minimum_state [T] T)
      : Circuit _ [T;T] T :=
      {{ fun input1 input2 =>
           let min1 := `minimum` input1 in
           let min2 := `minimum` input2 in
           let min1_le_min2 := `cmp` min1 min2 in
           if min1_le_min2 then min1 else min2
      }}.
  End CircuitDefinitions.

  Section SpecificationsAndProofs.
    Context {T : type}
            (* some order exists on type T *)
            (rankT : denote_type T -> N).
    Context (cmp : Circuit [] [T;T] Bit)
            {minimum_state} (minimum : Circuit minimum_state [T] T)
            {minimum_invariant : invariant_for minimum (list (denote_type T))}.

    (* high-level representation here is also the list of inputs so far *)
    Global Instance minimum_specification
      : specification_for minimum (list (denote_type T)) :=
      {| reset_repr := List.nil;
         update_repr :=
           fun (input : denote_type [T]) (acc : list (denote_type T)) =>
             let '(x,_) := input in
             x :: acc;
         precondition := fun _ _ => True;
         postcondition :=
           fun input acc out =>
             let '(x,_) := input in
             Forall (fun y => rankT out <= rankT y) (x :: acc);
      |}.

    (* Almost the same as minimum_specification *)
    Instance double_minimum_specification
      : specification_for (double_minimum cmp minimum) (list (denote_type T)) :=
      {| reset_repr := List.nil;
         update_repr :=
           fun (input : denote_type [T;T]) (acc : list (denote_type T)) =>
             let '(x,(y,_)) := input in
             x :: y :: acc;
         precondition := fun _ _ => True;
         postcondition :=
           fun input acc out =>
             let '(x,(y,_)) := input in
             Forall (fun y => rankT out <= rankT y) (x :: y :: acc);
      |}.

    Instance double_minimum_invariant
      : invariant_for (double_minimum cmp minimum) (list (denote_type T)) :=
      fun (state : denote_type (minimum_state ++ minimum_state ++ []))
        (acc : list (denote_type T)) =>
        let '(state1, state) := split_absorbed_denotation state in
        let '(state2, _) := split_absorbed_denotation state in
        exists acc1 acc2,
          minimum_invariant state1 acc1
          /\ minimum_invariant state2 acc2
          (* acc1 ++ acc2 is a permutation of acc *)
          /\ (forall x, In x (acc1 ++ acc2) -> In x acc)
          /\ (forall x, In x acc -> In x (acc1 ++ acc2)).

    Section Proofs.
      Context (cmp_correct :
                 forall x y, step cmp tt (x,(y,tt)) = (tt, rankT x <=? rankT y))
              (minimum_correctness : correctness_for minimum).
      Hint Rewrite cmp_correct : stepsimpl.

      Lemma split_combine_denotation
            {t1 t2} (x : denote_type t1) (y : denote_type t2) :
        split_absorbed_denotation (combine_absorbed_denotation x y) = (x,y).
      Proof.
        induction t1; destruct t2.
        all:cbn [split_absorbed_denotation combine_absorbed_denotation denote_type] in *.
        all:logical_simplify; subst.
        all:repeat lazymatch goal with x : unit |- _ => destruct x end.
        all:reflexivity.
      Qed.
      Lemma combine_split_denotation
            {t1 t2} (xy : denote_type (t1 ++ t2)) :
        combine_absorbed_denotation
          (fst (split_absorbed_denotation xy))
          (snd (split_absorbed_denotation xy)) = xy.
      Proof.
        induction t1; destruct t2.
        all:cbn [split_absorbed_denotation combine_absorbed_denotation
                                           denote_type absorb_any fst snd] in *.
        all:logical_simplify; subst.
        all:repeat lazymatch goal with x : unit |- _ => destruct x end.
        all:rewrite <-?surjective_pairing.
        all:reflexivity.
      Qed.

      Lemma double_minimum_invariant_at_reset
        : invariant_at_reset (double_minimum cmp minimum).
      Proof.
        simplify_invariant (double_minimum cmp minimum).
        cbn [double_minimum reset_state]. stepsimpl.
        rewrite !split_combine_denotation.
        exists nil, nil.
        ssplit.
        { exact (invariant_at_reset_pf (c:=minimum)). }
        { exact (invariant_at_reset_pf (c:=minimum)). }
        { cbn [app In]; tauto. }
        { cbn [reset_repr double_minimum_specification app In].
          tauto. }
      Qed.

      Lemma double_minimum_invariant_preserved : invariant_preserved (double_minimum cmp minimum).
      Proof.
        cbv [invariant_preserved]. cbn [absorb_any].
        intros [i1 [i2 []]].
        intros; subst. simplify_invariant (double_minimum cmp minimum).
        repeat destruct_pair_let.
        repeat lazymatch goal with
               | H : context [match ?p with pair _ _ => _ end] |- _ =>
                 rewrite (surjective_pairing p) in H
               end.
        cbv [double_minimum]. stepsimpl. logical_simplify; subst.
        repeat (destruct_pair_let; cbn [fst snd]). stepsimpl.
        repeat (rewrite split_combine_denotation; cbn [fst snd]).
        simplify_spec (double_minimum cmp minimum).
        do 2 eexists. ssplit.
        { eapply (invariant_preserved_pf (c:=minimum));
            [ | solve [eauto] .. ].
          simplify_spec minimum. reflexivity. }
        { eapply (invariant_preserved_pf (c:=minimum));
            [ | solve [eauto] .. ].
          simplify_spec minimum. reflexivity. }
        { cbn [app In]. intros.
          repeat match goal with
                 | _ => progress cbn [In] in *
                 | H : _ \/ _ |- _ => destruct H; subst
                 | H : In _ (_ ++ _) |- _ => eapply in_app_or in H
                 | H1 : (forall x, In x (_ ++ _) -> ?P), H2 : In ?x _ |- _ =>
                   assert ((fun x => P) x) by (apply H1; apply in_app_iff; tauto);
                     tauto
                 | _ => tauto
                 end. }
        { cbn [app In]. intros.
          rewrite in_app_iff. cbn [In].
          repeat match goal with
                 | _ => progress cbn [In] in *
                 | H : _ \/ _ |- _ => destruct H; subst
                 | H : In _ (_ ++ _) |- _ => eapply in_app_or in H
                 | H1 : (forall x, In x ?l -> ?P), H2 : In ?x ?l |- _ =>
                   specialize (H1 x H2)
                 | _ => tauto
                 end. }
      Qed.

      Lemma double_minimum_output_correct : output_correct (double_minimum cmp minimum).
      Proof.
        cbv [output_correct]. cbn [absorb_any].
        intros (i1,(i2,[])). intros.
        simplify_invariant (double_minimum cmp minimum).
        simplify_spec (double_minimum cmp minimum).
        repeat lazymatch goal with
               | H : context [match ?p with pair _ _ => _ end] |- _ =>
                 rewrite (surjective_pairing p) in H
               end.
        cbv [double_minimum]. stepsimpl. logical_simplify; subst.
        repeat (destruct_pair_let; cbn [fst snd]). stepsimpl.
        repeat use_correctness' minimum.
        rewrite !Forall_forall in *. intros.
        repeat match goal with
               | _ => progress cbn [In] in *
               | H : _ \/ _ |- _ => destruct H; subst
               | H : In _ (_ ++ _) |- _ => eapply in_app_or in H
               | H : forall x, ?y = x \/ _ -> _ |- _ <= rankT ?y =>
                 specialize (H y ltac:(eauto))
               | H : (forall x, (_ \/ In x ?l) -> _), H2 : In ?x ?l |- _ =>
                 specialize (H x ltac:(eauto))
               | H1 : (forall x, In x ?l -> ?P), H2 : In ?x ?l |- _ =>
                 specialize (H1 x H2)
               | _ => tauto
               | _ => lia
               | _ => solve [eauto using N.le_trans]
               | _ => destruct_one_match
               end.
      Qed.

      Existing Instances double_minimum_invariant_at_reset double_minimum_invariant_preserved
               double_minimum_output_correct.
      Global Instance double_minimum_correctness : correctness_for (double_minimum cmp minimum).
      Proof. constructor; typeclasses eauto. Defined.
    End Proofs.
  End SpecificationsAndProofs.

  Section Instantiations.
    Section CircuitDefinitions.
      Context {var : tvar}.
      Import ExprNotations.
      Import PrimitiveNotations.

      Definition minimum {T} (cmp : Circuit [] [T;T] Bit)
        : Circuit _ [T] T :=
        {{ fun input =>
             let/delay min :=
                (let input_le_min := `cmp` input min in
                 if input_le_min then input else min)
                  initially default in
             min
        }}.

      Definition cmp_bit : Circuit [] [Bit;Bit] Bit :=
        {{ fun x y => let out := (y || !x) in out }}.
      Definition cmp_bv {n} : Circuit [] [BitVec n;BitVec n] Bit :=
        {{ fun x y => let b := x <= y in b }}.

      (* Instantiate [minimum] and [double_minimum] for different types *)
      Definition minimum_bit : Circuit _ [Bit] Bit := minimum cmp_bit.
      Definition minimum_byte : Circuit _ [BitVec 8] (BitVec 8)
        := minimum cmp_bv.
      Definition double_minimum_bit : Circuit _ [Bit;Bit] Bit :=
        double_minimum cmp_bit minimum_bit.
      Definition double_minimum_byte : Circuit _ [BitVec 8;BitVec 8] (BitVec 8) :=
        double_minimum cmp_bv minimum_byte.
    End CircuitDefinitions.

    (* Parameterized proofs for [minimum] *)
    Section GeneralizedMinimum.
      Context {T} (rankT : denote_type T -> N)
              (rankT_default : rankT default = 0)
              (cmp : Circuit [] [T;T] Bit)
              (cmp_correct :
                 forall x y : denote_type T,
                   step cmp tt (x,(y,tt)) = (tt, rankT x <=? rankT y)).
      Hint Rewrite cmp_correct : stepsimpl.

      (* Generalized invariant for [minimum] *)
      Instance minimum_invariant
        : invariant_for (minimum cmp) (list (denote_type T)) :=
        fun (state : denote_type (T ++ [])) (acc : list (denote_type T)) =>
          let (min,_) := split_absorbed_denotation state in
          min = fold_right (fun x min =>
                              if rankT x <=? rankT min then x else min)
                           default acc.

      Lemma minimum_invariant_at_reset :
        invariant_at_reset (spec:=minimum_specification rankT (minimum cmp))
                           (minimum cmp).
      Proof.
        simplify_invariant (minimum cmp).
        cbn [minimum reset_state]. stepsimpl.
        rewrite !split_combine_denotation.
        reflexivity.
      Qed.

      Lemma minimum_invariant_preserved :
        invariant_preserved (spec:=minimum_specification rankT (minimum cmp))
                            (minimum cmp).
      Proof.
        simplify_invariant (minimum cmp). cbn [absorb_any].
        intros [input []].
        intros; subst. simplify_invariant (minimum cmp).
        repeat destruct_pair_let.
        repeat lazymatch goal with
               | H : context [match ?p with pair _ _ => _ end] |- _ =>
                 rewrite (surjective_pairing p) in H
               end.
        cbv [minimum]. stepsimpl. logical_simplify; subst.
        repeat (destruct_pair_let; cbn [fst snd]). stepsimpl.
        repeat (rewrite split_combine_denotation; cbn [fst snd]).
        cbn [update_repr minimum_specification].
        cbn [fold_right].
        lazymatch goal with H : _ = fold_right _ _ _ |- _ => rewrite <-H end.
        reflexivity.
      Qed.

      (* helper lemma for minimum_output_correct *)
      Lemma Forall_rankT_min min ls :
        min = fold_right (fun x min => if rankT x <=? rankT min then x else min) default ls ->
        Forall (fun y => rankT min <= rankT y) ls.
      Proof.
        revert min; induction ls; intros; [ solve [constructor] | ].
        subst. cbn [fold_right]. constructor; [ destruct_one_match; lia | ].
        destruct_one_match; [ | solve [eauto] ].
        specialize (IHls _ ltac:(reflexivity)).
        rewrite Forall_forall in IHls. apply Forall_forall; intros.
        specialize (IHls _ ltac:(eassumption)). lia.
      Qed.


      Lemma minimum_output_correct :
        output_correct (spec:=minimum_specification rankT (minimum cmp))
                       (minimum cmp).
      Proof.
        simplify_invariant (minimum cmp). cbn [absorb_any].
        intros [input []].
        intros; subst. cbn [postcondition precondition minimum_specification] in *.
        repeat destruct_pair_let.
        repeat lazymatch goal with
               | H : context [match ?p with pair _ _ => _ end] |- _ =>
                 rewrite (surjective_pairing p) in H
               end.
        cbv [minimum]. stepsimpl. logical_simplify; subst.
        repeat (destruct_pair_let; cbn [fst snd]). stepsimpl.
        apply Forall_rankT_min. cbn [fold_right].
        lazymatch goal with H : _ = fold_right _ _ _ |- _ => rewrite <-H end.
        reflexivity.
      Qed.

      Existing Instances minimum_invariant_at_reset minimum_invariant_preserved
               minimum_output_correct.
      Instance minimum_correctness :
        correctness_for (spec:=minimum_specification rankT (minimum cmp))
                        (minimum cmp).
      Proof. constructor; typeclasses eauto. Defined.
    End GeneralizedMinimum.

    Lemma cmp_bit_correct (x y : denote_type Bit) :
      step cmp_bit tt (x, (y, tt)) = (tt, N.b2n x <=? N.b2n y).
    Proof. destruct x, y; reflexivity. Qed.

    Lemma cmp_bv_correct n (x y : denote_type (BitVec n)) :
      step (cmp_bv (n:=n)) tt (x, (y, tt)) = (tt, x <=? y).
    Proof. reflexivity. Qed.

    (* Derive correctness for [minimum_bit] *)

    Global Instance minimum_bit_specification
      : specification_for minimum_bit (list bool) :=
      minimum_specification (T:=Bit) N.b2n minimum_bit.

    Global Instance minimum_bit_invariant : invariant_for minimum_bit (list bool) :=
      minimum_invariant (T:=Bit) N.b2n cmp_bit.

    Global Instance minimum_bit_correctness : correctness_for minimum_bit.
    Proof.
      apply @minimum_correctness; [ exact eq_refl | ].
      exact cmp_bit_correct.
    Qed.

    (* Derive correctness for [minimum_byte] *)
    Global Instance minimum_byte_specification
      : specification_for minimum_byte (list N) :=
      minimum_specification (T:=BitVec 8) (fun x => x) minimum_byte.

    Global Instance minimum_byte_invariant : invariant_for minimum_byte (list N) :=
      minimum_invariant (T:=BitVec 8) (fun x => x) cmp_bv.

    Global Instance minimum_byte_correctness : correctness_for minimum_byte.
    Proof.
      apply @minimum_correctness; [ exact eq_refl | ].
      exact (cmp_bv_correct 8).
    Defined.

    (* Derive correctness for [double_minimum_bit] *)

    Global Instance double_minimum_bit_specification
      : specification_for double_minimum_bit (list bool) :=
      double_minimum_specification (T:=Bit) N.b2n cmp_bit minimum_bit.

    Global Instance double_minimum_bit_invariant
      : invariant_for double_minimum_bit (list bool) :=
      double_minimum_invariant (T:=Bit) cmp_bit minimum_bit.

    Global Instance double_minimum_bit_correctness : correctness_for double_minimum_bit.
    Proof.
      apply @double_minimum_correctness; try typeclasses eauto.
      exact cmp_bit_correct.
    Defined.

    (* Derive correctness for [double_minimum_byte] *)

    Global Instance double_minimum_byte_specification
      : specification_for double_minimum_byte (list N) :=
      double_minimum_specification (T:=BitVec 8) (fun x => x) cmp_bv minimum_byte.

    Global Instance double_minimum_byte_invariant
      : invariant_for double_minimum_byte (list N) :=
      double_minimum_invariant (T:=BitVec 8) cmp_bv minimum_byte.

    Global Instance double_minimum_byte_correctness : correctness_for double_minimum_byte.
    Proof.
      apply @double_minimum_correctness; try typeclasses eauto.
      exact (cmp_bv_correct 8).
    Defined.
  End Instantiations.

End AbstractSubcircuitExample.
