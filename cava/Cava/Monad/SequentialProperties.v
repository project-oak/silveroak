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

Require Import Coq.Lists.List.
Import ListNotations.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.IdentityMonad.
Export MonadNotation.

Require Import Cava.Cava.
Require Import Cava.Signal.
Require Import Cava.Tactics.
Require Import Cava.Monad.Identity.
Require Import Cava.Monad.CavaClass.
Require Import Cava.Monad.Sequential.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Cava.ListUtils.

(* Helpful tactics for simplifying sequential goals *)
Ltac seqsimpl_step :=
  first [ progress cbn beta iota delta
                   [fst snd hd tl sequential SequentialSemantics]
        | progress autorewrite with seqsimpl
        | progress destruct_pair_let
        | progress simpl_ident ].
Ltac seqsimpl := repeat seqsimpl_step.

Section Overlap.
  Lemma overlap_cons1 {A} n (xs ys : seqType A) x :
    n <= length xs ->
    overlap n (x :: xs) ys = x :: overlap n xs (tl ys).
  Proof.
    intros; cbv [overlap]. cbn [length].
    rewrite Nat.sub_succ_l by lia. rewrite app_comm_cons.
    replace (n - length xs) with 0 by lia.
    replace (n - S (length xs)) with 0 by lia.
    cbn [repeat].
    destruct ys; cbn [skipn tl];
      [ rewrite skipn_nil; reflexivity | ].
    reflexivity.
  Qed.

  Lemma overlap_cons2 {A} n (xs ys : seqType A) :
    length xs <= n ->
    overlap n xs ys = xs ++ repeat (defaultCombValue A) (n - length xs) ++ ys.
  Proof.
    intros; cbv [overlap]. cbn [length].
    replace (length xs - n) with 0 by lia.
    reflexivity.
  Qed.

  Lemma overlap_0_nil {A} (x : seqType A) : overlap 0 [] x = x.
  Proof.
    cbv [overlap]. cbn [length].
    rewrite Nat.sub_0_l. cbn [skipn].
    reflexivity.
  Qed.

  Lemma overlap_app_same {A} (x y : seqType A) :
    overlap 0 x (x ++ y) = x ++ y.
  Proof.
    cbv [overlap]. rewrite Nat.sub_0_l, Nat.sub_0_r.
    cbn [repeat]. rewrite skipn_app, Nat.sub_diag.
    rewrite skipn_all.
    cbn [skipn]. reflexivity.
  Qed.

  Lemma overlap_nil_r {A} n (x : seqType A) :
    n <= length x -> overlap n x [] = x.
  Proof.
    intros. cbv [overlap]. cbn [length].
    rewrite skipn_nil, app_nil_r.
    replace (n - length x) with 0 by lia.
    cbn [repeat]. rewrite app_nil_r.
    reflexivity.
  Qed.

  Lemma overlap_assoc {A} n m (x y z : seqType A) :
    overlap n x (overlap m y z) = overlap (n + m) (overlap n x y) z.
  Proof.
    cbv [overlap]. intros.
    rewrite !app_assoc.
    autorewrite with push_skipn push_length natsimpl.
    rewrite <-!app_assoc.
    change CombinationalMonad.combType with Signal.combType in *.
    repeat (f_equal; try lia).
  Qed.
End Overlap.
Hint Rewrite @overlap_cons1 @overlap_cons2 @overlap_nil_r
     using solve [length_hammer] : seqsimpl.
Hint Rewrite @overlap_0_nil @overlap_app_same using solve [eauto] : seqsimpl.

Section Loops.
  Lemma loopSeq'_step {A B C}
        (f : seqType A * seqType C -> ident (seqType B * seqType C))
        (spec : combType A -> combType C -> seqType B * seqType C) :
    (forall a c, sequential (f ([a], [c])) = spec a c) ->
    forall (loop_state : nat * ident (seqType B * seqType C)) a,
      loopSeq' f loop_state a
      = let t := fst loop_state in
        let '(acc, feedback) := unIdent (snd loop_state) in
        let c := hd (defaultCombValue C) feedback in
        let r := spec a c in
        (S t, ret (overlap t acc (fst r), overlap 0 (tl feedback) (snd r))).
  Proof.
    cbv [sequential loopSeq' SequentialSemantics]. intro Hfspec.
    intros. seqsimpl. rewrite Hfspec. reflexivity.
  Qed.

  Lemma loop_stepwise {A B C}
        (f : seqType A * seqType C -> ident (seqType B * seqType C))
        (spec : combType A -> combType C -> seqType B * seqType C)
        input :
    (forall a c, sequential (f ([a], [c])) = spec a c) ->
    sequential (loopDelay (CavaSeq:=SequentialSemantics) f input)
    = snd (fst (fold_left (fun loop_state a =>
                             let '(t, acc, feedback) := loop_state in
                             let c := hd (defaultCombValue C) feedback in
                             let r := spec a c in
                             (S t, overlap t acc (fst r), overlap 0 (tl feedback) (snd r)))
                          input (0, [], [defaultCombValue C]))).
  Proof.
    cbv [loopDelay loopSeq SequentialSemantics sequential]; intros.
    seqsimpl.
    erewrite fold_left_ext with (f0:=loopSeq' _) by (apply loopSeq'_step; eassumption).
    factor_out_loops.
    eapply fold_left_double_invariant
      with(I:=fun (x : nat * seqType B * seqType C) (y : nat * ident (seqType B * seqType C)) =>
                x = (fst y, fst (unIdent (snd y)), snd (unIdent (snd y)))).
    { (* invariant holds at start *)
      reflexivity. }
    { (* invariant holds through loop *)
    intros; repeat destruct_pair_let. subst.
    seqsimpl. reflexivity. }
  { (* invariant implies postcondition *)
    intros. subst. seqsimpl. reflexivity. }
  Qed.

  Lemma loop_stepwise_indexed {A B C}
        (f : seqType A * seqType C -> ident (seqType B * seqType C))
        (spec : combType A -> combType C -> seqType B * seqType C)
        input :
    (forall a c, sequential (f ([a], [c])) = spec a c) ->
    sequential (loopDelay (CavaSeq:=SequentialSemantics) f input)
    = fst (fold_left (fun loop_state t =>
                        let '(acc, feedback) := loop_state in
                        let a := nth t input (defaultCombValue A) in
                        let c := hd (defaultCombValue C) feedback in
                        let r := spec a c in
                        (overlap t acc (fst r), overlap 0 (tl feedback) (snd r)))
                     (seq 0 (length input))
                     ([], [defaultCombValue C])).
  Proof.
    intros. erewrite loop_stepwise by eassumption.
    erewrite fold_left_to_seq with (ls:=input) (default:=defaultCombValue A).
    pose (R:=fun t (x : seqType B * seqType C) (y : nat * seqType B * seqType C) =>
               y = (t, fst x, snd x)).
    factor_out_loops.
    lazymatch goal with
    | |- ?P ?loop1 ?loop2 =>
      let H := fresh in
      assert (R (length input) loop1 loop2) as H;
        (* prove that R implies postcondition *)
        [ | subst R; cbv beta in *; rewrite H; reflexivity ]
    end.
    eapply fold_left_preserves_relation_seq with (R0:=R).
    { (* R holds at start *)
      reflexivity. }
    { (* R holds through loop *)
      subst R. cbv beta zeta.
      intros. repeat destruct_pair_let. subst.
      reflexivity. }
  Qed.

  Lemma loop_invariant {A B C}
        (I : nat -> seqType B -> seqType C -> Prop)
        (f : seqType A * seqType C -> ident (seqType B * seqType C))
        (P : seqType B -> Prop) input :
    (* invariant is true for start state *)
    I 0 [] [defaultCombValue C] ->
    (* invariant holds through loop *)
    (forall t b c,
        I t b c ->
        t < length input ->
        let a := nth t input (defaultCombValue A) in
        let x := hd (defaultCombValue C) c in
        let r := sequential (f ([a], [x])) in
        I (S t) (overlap t b (fst r)) (overlap 0 (tl c) (snd r))) ->
    (* invariant is strong enough to prove postcondition *)
    (forall b c, I (length input) b c -> P b) ->
    P (sequential (loopDelay (CavaSeq:=SequentialSemantics) f input)).
  Proof.
    intros Hstart Hbody Hpost.
    erewrite loop_stepwise_indexed by (intros; reflexivity).
    cbv beta.
    eapply fold_left_invariant_seq with
        (I0:=fun t '(b,c) => I t b c).
    { assumption. }
    { intros *; repeat destruct_pair_let; intros.
      seqsimpl. apply Hbody; eauto; lia. }
    { intros *; repeat destruct_pair_let; intros.
      eauto. }
  Qed.

  (* More flexible than loop_invariant about the start state satisfying the invariant *)
  Lemma loop_invariant_alt {A B C}
        (I : nat -> seqType B -> seqType C -> Prop)
        (f : seqType A * seqType C -> ident (seqType B * seqType C))
        (P : seqType B -> Prop) input :
    (* Either the input is nil and P holds on nil, or the invariant is satisfied
       after one step *)
    (match input with
     | [] => P []
     | i0 :: _ =>
       let r := sequential (f ([i0], [defaultCombValue C])) in
       I 1 (fst r) (snd r)
     end) ->
    (* invariant holds through loop *)
    (forall t b c,
        I t b c ->
        t < length input ->
        let a := nth t input (defaultCombValue A) in
        let x := hd (defaultCombValue C) c in
        let r := sequential (f ([a], [x])) in
        I (S t) (overlap t b (fst r)) (overlap 0 (tl c) (snd r))) ->
    (* invariant is strong enough to prove postcondition *)
    (forall b c, I (length input) b c -> P b) ->
    P (sequential (loopDelay (CavaSeq:=SequentialSemantics) f input)).
  Proof.
    intros Hstart Hbody Hpost.
    erewrite loop_stepwise_indexed by (intros; reflexivity).
    destruct input; [ cbn [fold_left]; seqsimpl; assumption | ].
    cbn [fold_left seq length]. seqsimpl.
    eapply fold_left_invariant_seq with
        (I0:=fun t '(b,c) => I t b c).
    { apply Hstart. }
    { intros *; repeat destruct_pair_let; intros.
      apply Hbody; eauto using in_cons; length_hammer. }
    { intros *; repeat destruct_pair_let; intros.
      eauto. }
  Qed.
End Loops.
