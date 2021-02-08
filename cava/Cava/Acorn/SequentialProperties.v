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
Require Import coqutil.Tactics.Tactics.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.IdentityMonad.
Export MonadNotation.

Require Import Cava.Cava.
Require Import Cava.Tactics.
Require Import Cava.Acorn.Identity.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.CavaPrelude.
Require Import Cava.Acorn.Combinators.
Require Import Cava.Acorn.CombinationalMonad.
Require Import Cava.Acorn.CombinationalProperties.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Cava.ListUtils.

(* Helpful tactics for simplifying semantics goals *)
Ltac seqsimpl_step :=
  first [ progress cbn beta iota delta
                   [fst snd hd tl semantics CircuitSemantics]
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

  Lemma overlap_snoc_cons {A} n (xs ys : seqType A) x y :
    length xs = n ->
    overlap n (xs ++ [x]) (y :: ys) = xs ++ x :: ys.
  Proof.
    intros; cbv [overlap]. cbn [length].
    autorewrite with push_length. subst.
    match goal with |- context [repeat _ ?n] =>
                    replace n with 0 by lia end.
    cbn [repeat app].
    match goal with |- context [?n + 1 - ?n] =>
                    replace (n + 1 - n) with 1 by lia end.
    cbn [skipn]. rewrite <-app_assoc.
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
    repeat (f_equal; try lia).
  Qed.

  Lemma skipn_overlap_same {A} n (x y : seqType A) :
    skipn n (overlap n x y) = overlap 0 (skipn n x) y.
  Proof.
    cbv [overlap]. intros.
    autorewrite with push_skipn push_length natsimpl.
    reflexivity.
  Qed.

  Lemma overlap_length {A} n x y :
    length (@overlap A n x y) = Nat.max (length x) (length y + n).
  Proof.
    cbv [overlap]. autorewrite with push_length. lia.
  Qed.
  Hint Rewrite @overlap_length using solve [eauto] : push_length.

  Lemma overlap_repeat {A} n m p (x : combType A) :
    n <= m ->
    overlap n (repeat x m) (repeat x p) = repeat x (Nat.max m (p + n)).
  Proof.
    intros; cbv [overlap]. autorewrite with push_length natsimpl.
    cbn [repeat app]. rewrite skipn_repeat, <-repeat_append.
    f_equal; lia.
  Qed.

  Lemma overlap_mkpair_repeat_l {A B} (x : combType A) (b1 b2 : seqType B)
        offset n m :
    length b1 = n -> length b2 = m -> offset <= length b1 ->
    overlap offset (mkpair (repeat x n) b1) (mkpair (repeat x m) b2)
    = mkpair (repeat x (Nat.max n (m + offset))) (overlap offset b1 b2).
  Proof.
    intros. cbn [mkpair CircuitSemantics].
    rewrite !pad_combine_eq by length_hammer.
    cbv [overlap]. cbn [combType] in *.
    autorewrite with push_length natsimpl push_skipn.
    rewrite (proj2 (Nat.sub_0_le offset (length b1))) by lia.
    cbn [repeat app]. rewrite <-combine_append, <-repeat_append by length_hammer.
    subst; f_equal; [ ]. f_equal; lia.
  Qed.

  Lemma unpair_overlap_mkpair_r {A B} offset ab (a : seqType A) (b : seqType B) :
    unpair (overlap offset ab (mkpair a b)) = (overlap offset (fst (unpair ab))
                                                       (extend a (lastSignal a) (length b)),
                                               overlap offset (snd (unpair ab))
                                                       (extend b (lastSignal b) (length a))).
  Proof.
    cbv [overlap]; intros. cbn [unpair mkpair CircuitSemantics].
    cbn [seqType combType defaultCombValue] in *. cbv [pad_combine].
    autorewrite with push_split. cbn [fst snd].
    cbv [seqType]. cbn [combType defaultCombValue] in *.
    rewrite split_length_r, split_length_l.
    rewrite combine_split by apply extend_to_match.
    reflexivity.
  Qed.

  Lemma unpair_overlap_mkpair_r_same {A B} offset ab (a : seqType A) (b : seqType B) :
    length a = length b ->
    unpair (overlap offset ab (mkpair a b)) = (overlap offset (fst (unpair ab)) a,
                                               overlap offset (snd (unpair ab)) b).
  Proof.
    intros. rewrite unpair_overlap_mkpair_r.
    rewrite !extend_le by lia. reflexivity.
  Qed.
End Overlap.
Hint Rewrite @overlap_cons1 @overlap_cons2 @overlap_nil_r @overlap_snoc_cons
     using solve [length_hammer] : seqsimpl.
Hint Rewrite @overlap_0_nil @overlap_app_same using solve [eauto] : seqsimpl.
Hint Rewrite @skipn_overlap_same using solve [eauto] : push_skipn.
Hint Rewrite @overlap_length using solve [eauto] : push_length.

Section Loops.
  Lemma loopSeqS'_step {A B}
        (resetval : combType B)
        (f : seqType A * seqType B -> ident (seqType B))
        (spec : combType A -> combType B -> seqType B) :
    (forall a b, semantics (f ([a], [b])) = spec a b) ->
    forall (loop_state : nat * ident (seqType B)) a,
      loopSeqS' resetval f loop_state a
      = let t := fst loop_state in
        let acc := unIdent (snd loop_state) in
        let feedback := match t with
                        | 0 => resetval
                        | S t' => nth t' acc (defaultCombValue B)
                        end in
        let r := spec a feedback in
        (S t, ret (overlap t acc r)).
  Proof.
    cbv [semantics loopSeqS' CircuitSemantics]. intro Hfspec.
    intros. seqsimpl. rewrite Hfspec. reflexivity.
  Qed.

  Lemma loopDelaySR_stepwise {A B}
        (resetval : combType B)
        (f : seqType A * seqType B -> ident (seqType B))
        (spec : combType A -> combType B -> seqType B)
        input :
    (forall a b, semantics (f ([a], [b])) = spec a b) ->
    semantics (loopDelaySR (Cava:=CircuitSemantics) resetval f input)
    = snd (fold_left (fun loop_state a =>
                        let '(t, acc) := loop_state in
                        let feedback := match t with
                                        | 0 => resetval
                                        | S t' => nth t' acc (defaultCombValue B)
                                        end in
                        let r := spec a feedback in
                        (S t, overlap t acc r))
                     input (0, [])).
  Proof.
    cbv [loopDelaySR loopSeqS CircuitSemantics semantics]; intros.
    seqsimpl.
    erewrite fold_left_ext with (f0:=loopSeqS' _ _) by (apply loopSeqS'_step; eassumption).
    factor_out_loops.
    eapply fold_left_double_invariant
      with(I:=fun (x : nat * seqType B) (y : nat * ident (seqType B)) =>
                x = (fst y, unIdent (snd y))).
    { (* invariant holds at start *)
      reflexivity. }
    { (* invariant holds through loop *)
      intros; repeat destruct_pair_let. subst.
      seqsimpl. reflexivity. }
  { (* invariant implies postcondition *)
    intros. subst. seqsimpl. reflexivity. }
  Qed.

  Lemma loopDelaySR_stepwise_indexed {A B}
        (resetval : combType B)
        (f : seqType A * seqType B -> ident (seqType B))
        (spec : combType A -> combType B -> seqType B)
        input :
    (forall a b, semantics (f ([a], [b])) = spec a b) ->
    semantics (loopDelaySR resetval f input)
    = fold_left (fun acc t =>
                   let a := nth t input (defaultCombValue A) in
                   let feedback := match t with
                                   | 0 => resetval
                                   | S t' => nth t' acc (defaultCombValue B)
                                   end in
                   let r := spec a feedback in
                   overlap t acc r)
                (seq 0 (length input)) [].
  Proof.
    intros. erewrite loopDelaySR_stepwise by eassumption.
    erewrite fold_left_to_seq with (ls:=input) (default:=defaultCombValue A).
    pose (R:=fun t (x : seqType B) (y : nat * seqType B) => y  = (t, x)).
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

  Lemma loopDelayS_stepwise {A B}
        (f : seqType A * seqType B -> ident (seqType B))
        (spec : combType A -> combType B -> seqType B)
        input :
    (forall a b, semantics (f ([a], [b])) = spec a b) ->
    semantics (loopDelayS f input)
    = snd (fold_left (fun loop_state a =>
                        let '(t, acc) := loop_state in
                        let feedback := match t with
                                        | 0 => defaultCombValue B
                                        | S t' => nth t' acc (defaultCombValue B)
                                        end in
                        let r := spec a feedback in
                        (S t, overlap t acc r))
                     input (0, [])).
  Proof. cbv [loopDelayS]. apply loopDelaySR_stepwise. Qed.

  Lemma loopDelayS_stepwise_indexed {A B}
        (f : seqType A * seqType B -> ident (seqType B))
        (spec : combType A -> combType B -> seqType B)
        input :
    (forall a b, semantics (f ([a], [b])) = spec a b) ->
    semantics (loopDelayS f input)
    = fold_left (fun acc t =>
                   let a := nth t input (defaultCombValue A) in
                   let feedback := match t with
                                   | 0 => defaultCombValue B
                                   | S t' => nth t' acc (defaultCombValue B)
                                   end in
                   let r := spec a feedback in
                   overlap t acc r)
                (seq 0 (length input)) [].
  Proof. cbv [loopDelayS]. apply loopDelaySR_stepwise_indexed. Qed.

  Lemma loopDelayS_invariant {A B}
        (I : nat -> seqType B  -> Prop)
        (f : seqType A * seqType B -> ident (seqType B))
        (P : seqType B -> Prop) input :
    (* invariant is true for start state *)
    I 0 [] ->
    (* invariant holds through loop *)
    (forall t acc,
        I t acc ->
        t < length input ->
        let a := nth t input (defaultCombValue A) in
        let feedback := match t with
                        | 0 => defaultCombValue B
                        | S t' => nth t' acc (defaultCombValue B)
                        end in
        let r := semantics (f ([a], [feedback])) in
        I (S t) (overlap t acc r)) ->
    (* invariant is strong enough to prove postcondition *)
    (forall b, I (length input) b -> P b) ->
    P (semantics (loopDelayS f input)).
  Proof.
    intros Hstart Hbody Hpost.
    erewrite loopDelayS_stepwise_indexed by (intros; reflexivity).
    cbv beta. eapply fold_left_invariant_seq with (I0 := I).
    { assumption. }
    { intros *; repeat destruct_pair_let; intros.
      seqsimpl. apply Hbody; eauto; lia. }
    { intros *; repeat destruct_pair_let; intros.
      eauto. }
  Qed.

  (* More flexible than loop_invariant about the start state satisfying the invariant *)
  Lemma loopDelayS_invariant_alt {A B}
        (I : nat -> seqType B -> Prop)
        (f : seqType A * seqType B -> ident (seqType B))
        (P : seqType B -> Prop) input :
    (* Either the input is nil and P holds on nil, or the invariant is satisfied
       after one step *)
    (match input with
     | [] => P []
     | i0 :: _ =>
       I 1 (semantics (f ([i0], [defaultCombValue B])))
     end) ->
    (* invariant holds through loop *)
    (forall t acc,
        I t acc ->
        0 < t < length input ->
        let a := nth t input (defaultCombValue A) in
        let feedback := match t with
                        | 0 => defaultCombValue B
                        | S t' => nth t' acc (defaultCombValue B)
                        end in
        let r := semantics (f ([a], [feedback])) in
        I (S t) (overlap t acc r)) ->
    (* invariant is strong enough to prove postcondition *)
    (forall b, I (length input) b -> P b) ->
    P (semantics (loopDelayS f input)).
  Proof.
    intros Hstart Hbody Hpost.
    erewrite loopDelayS_stepwise_indexed by (intros; reflexivity).
    destruct input; [ cbn [fold_left]; seqsimpl; assumption | ].
    cbn [fold_left seq length]. seqsimpl.
    eapply fold_left_invariant_seq with (I0:=I).
    { apply Hstart. }
    { intros *; repeat destruct_pair_let; intros.
      apply Hbody; eauto using in_cons; length_hammer. }
    { intros *; repeat destruct_pair_let; intros.
      eauto. }
  Qed.

  Lemma loopDelay_invariant {A B C}
        (I : nat -> seqType B -> seqType C -> Prop)
        (f : seqType A * seqType C -> ident (seqType B * seqType C))
        (P : seqType B -> Prop) input :
    (* TODO(jadep): this precondition can be removed if mkpair is changed from
       combine (truncating) to something that pads the lists to the same length
       before combining them. *)
    (* function produces same number of results for feedback and output *)
    (forall a c, length (fst (unIdent (f ([a],[c]))))
            = length (snd (unIdent (f ([a],[c]))))) ->
    (* invariant is true for start state *)
    I 0 [] [] ->
    (* invariant holds through loop *)
    (forall t b c,
        I t b c ->
        t < length input ->
        let a := nth t input (defaultCombValue A) in
        let x := hd (defaultCombValue C) c in
        let r := semantics (f ([a], [x])) in
        I (S t) (overlap t b (fst r)) (overlap 0 (tl c) (snd r))) ->
    (* invariant is strong enough to prove postcondition *)
    (forall b c, I (length input) b c -> P b) ->
    P (semantics (loopDelay f input)).
  Proof.
    intros ? ? Hbody; intros; cbv [loopDelay semantics]. seqsimpl.
    eapply loopDelayS_invariant
      with (I0:=fun t (bc : seqType (Pair B C)) =>
                  (t = 0 -> bc = nil) /\
                  I t (fst (unpair bc)) (match t with
                                         | 0 => []
                                         | S t' => snd (unpair (skipn t' bc))
                                         end)).
    { split; tauto || assumption. }
    { cbv zeta; intros *. intros [Ht0 HI]. intros.
      split; [ congruence | ]. repeat destruct_pair_let.
      cbv [semantics]; seqsimpl. rewrite unpair_skipn.
      rewrite !unpair_overlap_mkpair_r_same
        by (destruct t; cbn [unpair split CircuitSemantics];
            destruct_one_match; cbn [fst snd]; auto).
      cbn [fst snd]. autorewrite with push_skipn. cbv zeta in Hbody.
      specialize (Hbody _ _ _ ltac:(eassumption) ltac:(eassumption)).
      (* Some unfortunately specific and manual replaces to make invariant
         expressions match *)
      match goal with
      | H : context [f (?x, ?y1)] |- context [f (?x, ?y2)] =>
        replace y2 with y1
      end.
      2:{ destruct_one_match; autorewrite with push_skipn;
          [ reflexivity | ]. rewrite unpair_skipn.
          cbn [defaultCombValue combType fst snd].
          rewrite split_nth. cbn [fst snd].
          rewrite hd_skipn. reflexivity. }
      match goal with
      | H : context [overlap 0 ?x1 ?y] |- context [overlap 0 ?x2 ?y] =>
        replace x2 with x1
      end.
      2:{ destruct_one_match; [ rewrite Ht0 by reflexivity; reflexivity | ].
          rewrite unpair_skipn. cbn [snd].
          rewrite tl_skipn.  reflexivity. }
      apply Hbody. }
    { intros *. intros [? ?]. intros.
      eauto. }
  Qed.

  (* More flexible than loop_invariant about the start state satisfying the invariant *)
  Lemma loop_invariant_alt {A B C}
        (I : nat -> seqType B -> seqType C -> Prop)
        (f : seqType A * seqType C -> ident (seqType B * seqType C))
        (P : seqType B -> Prop) input :
    (* TODO(jadep): this precondition can be removed if mkpair is changed from
       combine (truncating) to something that pads the lists to the same length
       before combining them. *)
    (* function produces same number of results for feedback and output *)
    (forall a c, length (fst (unIdent (f ([a],[c]))))
            = length (snd (unIdent (f ([a],[c]))))) ->
    (* Either the input is nil and P holds on nil, or the invariant is satisfied
       after one step *)
    (match input with
     | [] => P []
     | i0 :: _ =>
       let r := semantics (f ([i0], [defaultCombValue C])) in
       I 1 (fst r) (snd r)
     end) ->
    (* invariant holds through loop *)
    (forall t b c,
        I t b c ->
        0 < t < length input ->
        let a := nth t input (defaultCombValue A) in
        let x := hd (defaultCombValue C) c in
        let r := semantics (f ([a], [x])) in
        I (S t) (overlap t b (fst r)) (overlap 0 (tl c) (snd r))) ->
    (* invariant is strong enough to prove postcondition *)
    (forall b c, I (length input) b c -> P b) ->
    P (semantics (loopDelay f input)).
  Proof.
    intros ? ? Hbody; intros; cbv [loopDelay semantics]. seqsimpl.
    eapply loopDelayS_invariant_alt
      with (I0:=fun t (bc : seqType (Pair B C)) =>
                  I t (fst (unpair bc)) (match t with
                                         | 0 => []
                                         | S t' => snd (unpair (skipn t' bc))
                                         end)).
    { destruct input; [ solve [auto] | ].
      repeat destruct_pair_let.
      cbv zeta in *. cbn [semantics unIdent].
      autorewrite with push_skipn.
      rewrite unpair_mkpair
        by (cbn [unpair split CircuitSemantics];
            destruct_one_match; cbn [fst snd]; auto).
      cbn [fst snd]. auto. }
    { cbv zeta; intros. repeat destruct_pair_let.
      cbv [semantics]; seqsimpl. rewrite unpair_skipn.
      rewrite !unpair_overlap_mkpair_r_same
        by (destruct t; cbn [unpair split CircuitSemantics];
            destruct_one_match; cbn [fst snd]; auto).
      cbn [fst snd]. autorewrite with push_skipn. cbv zeta in Hbody.
      specialize (Hbody _ _ _ ltac:(eassumption) ltac:(eassumption)).
      (* Some unfortunately specific and manual replaces to make invariant
         expressions match *)
      match goal with
      | H : context [f (?x, ?y1)] |- context [f (?x, ?y2)] =>
        replace y2 with y1
      end.
      2:{ destruct_one_match; autorewrite with push_skipn;
          [ reflexivity | ]. rewrite unpair_skipn.
          cbn [defaultCombValue combType fst snd].
          rewrite split_nth. cbn [fst snd].
          rewrite hd_skipn. reflexivity. }
      match goal with
      | H : context [overlap 0 ?x1 ?y] |- context [overlap 0 ?x2 ?y] =>
        replace x2 with x1
      end.
      2:{ destruct_one_match; [ lia | ].
          rewrite unpair_skipn. cbn [snd].
          rewrite tl_skipn.  reflexivity. }
      apply Hbody. }
    { intros; eauto. }
  Qed.
End Loops.

Section Evaluation.
  Lemma semantics_compose {A B C}
        (f : A -> cava B)
        (g : B -> cava C) i :
    semantics ((f >=> g) i) = semantics (g (semantics (f i))).
  Proof. reflexivity. Qed.

  Lemma delayCorrect {A} (i : seqType A) :
    semantics (delay i) = defaultCombValue A :: i.
  Proof. reflexivity. Qed.

  Lemma fork2Correct {A} (i : seqType A) :
    semantics (fork2 i) = (i, i).
  Proof. reflexivity. Qed.

  Lemma unpair_single {A B} (p : combType (Pair A B)) :
    unpair [p] = ([fst p], [snd p]).
  Proof. destruct p; reflexivity. Qed.
End Evaluation.
Hint Rewrite @semantics_compose @delayCorrect @fork2Correct @unpair_single
     using solve [eauto] : seqsimpl.
