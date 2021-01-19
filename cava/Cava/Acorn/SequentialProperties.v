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
Require Import Cava.Signal.
Require Import Cava.Tactics.
Require Import Cava.Acorn.Identity.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.Combinators.
Require Import Cava.Acorn.Sequential.

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

Section PeelSignals.
  Lemma peel_unpeel_signals {A} (i : list (@signals combType _ A)) :
    peel_signals (unpeel_signals i) = i.
  Proof.
    revert i; induction A; intros; [ reflexivity | ].
    cbn [peel_signals unpeel_signals].
    repeat destruct_pair_let. cbn [fst snd].
    rewrite IHA1, IHA2.
    (* this annoying manipulation is necessary because split_combine has a match *)
    pose proof (split_combine i) as Hsplit.
    rewrite (surjective_pairing (split i)) in Hsplit.
    exact Hsplit.
  Qed.

  Fixpoint uniform_length {A : SignalInterface} (n : nat)
    : @signals seqType _ A -> Prop :=
    match A as A return signals A -> Prop with
    | ione t => fun x : seqType t => length x = n
    | ipair t1 t2 =>
      fun x => uniform_length n (fst x) /\ uniform_length n (snd x)
    end.

  Lemma peel_signals_length {A} n (i : @signals seqType _ A) :
    uniform_length n i -> length (peel_signals i) = n.
  Proof.
    revert i; induction A; cbn [uniform_length peel_signals]; [ tauto | ].
    destruct 1; intros. cbn [signals signals_gen].
    rewrite combine_length, IHA1, IHA2 by auto.
    lia.
  Qed.

  Lemma unpeel_peel_signals {A} n (i : @signals seqType _ A) :
    uniform_length n i ->
    unpeel_signals (peel_signals i) = i.
  Proof.
    revert i; induction A; [ reflexivity | ].
    cbn [peel_signals unpeel_signals uniform_length].
    destruct 1; intros.
    repeat destruct_pair_let. cbn [fst snd].
    rewrite combine_split by (erewrite !peel_signals_length by eauto; lia).
    cbn [fst snd]. rewrite IHA1, IHA2 by auto.
    destruct i; reflexivity.
  Qed.

  Lemma uniform_length_unpeel {A} (i : list (@signals combType _ A)) n:
    length i = n ->
    uniform_length n (unpeel_signals i).
  Proof.
    revert n i; induction A; [ intros; subst; reflexivity | ].
    intros; cbn [uniform_length unpeel_signals].
    repeat destruct_pair_let; cbn [fst snd].
    split; [ apply IHA1 | apply IHA2 ]; length_hammer.
  Qed.
End PeelSignals.
Hint Rewrite @peel_signals_length using solve [eauto] : push_length.

Section Overlap.
  Lemma overlap_cons1 {A} n (xs ys : list (signals A)) x :
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

  Lemma overlap_cons2 {A} n (xs ys : list (signals A)) :
    length xs <= n ->
    overlap n xs ys = xs ++ repeat (defaultSignals A) (n - length xs) ++ ys.
  Proof.
    intros; cbv [overlap]. cbn [length].
    replace (length xs - n) with 0 by lia.
    reflexivity.
  Qed.

  Lemma overlap_snoc_cons {A} n (xs ys : list (signals A)) x y :
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

  Lemma overlap_0_nil {A} (x : list (signals A)) : overlap 0 [] x = x.
  Proof.
    cbv [overlap]. cbn [length].
    rewrite Nat.sub_0_l. cbn [skipn].
    reflexivity.
  Qed.

  Lemma overlap_app_same {A} (x y : list (signals A)) :
    overlap 0 x (x ++ y) = x ++ y.
  Proof.
    cbv [overlap]. rewrite Nat.sub_0_l, Nat.sub_0_r.
    cbn [repeat]. rewrite skipn_app, Nat.sub_diag.
    rewrite skipn_all.
    cbn [skipn]. reflexivity.
  Qed.

  Lemma overlap_nil_r {A} n (x : list (signals A)) :
    n <= length x -> overlap n x [] = x.
  Proof.
    intros. cbv [overlap]. cbn [length].
    rewrite skipn_nil, app_nil_r.
    replace (n - length x) with 0 by lia.
    cbn [repeat]. rewrite app_nil_r.
    reflexivity.
  Qed.

  Lemma overlap_assoc {A} n m (x y z : list (signals A)) :
    overlap n x (overlap m y z) = overlap (n + m) (overlap n x y) z.
  Proof.
    cbv [overlap]. intros.
    rewrite !app_assoc.
    autorewrite with push_skipn push_length natsimpl.
    rewrite <-!app_assoc.
    repeat (f_equal; try lia).
  Qed.

  Lemma skipn_overlap_same {A} n (x y : list (signals A)) :
    skipn n (overlap n x y) = overlap 0 (skipn n x) y.
  Proof.
    cbv [overlap]. intros.
    autorewrite with push_skipn push_length natsimpl.
    reflexivity.
  Qed.

  Lemma skipn_overlap_signals_same {A} n (x y : @signals seqType _ A) :
    skipn n (peel_signals (overlap_signals n x y))
    = peel_signals (overlap_signals 0 (unpeel_signals (skipn n (peel_signals x))) y).
  Proof.
    cbv [overlap_signals]. intros. rewrite !peel_unpeel_signals.
    rewrite skipn_overlap_same. reflexivity.
  Qed.

  Lemma overlap_length {A} offset (a1 a2 : list (signals A)) :
    length (overlap offset a1 a2) = Nat.max (length a1) (length a2 + offset).
  Proof. cbv [overlap]; length_hammer. Qed.

  Lemma uniform_length_overlap_signals {A} offset (a1 a2 : @signals seqType _ A) n1 n2 n :
    uniform_length n1 a1 -> uniform_length n2 a2 -> n = Nat.max n1 (n2 + offset) ->
    uniform_length n (overlap_signals offset a1 a2).
  Proof.
    intros; cbv [overlap_signals].
    apply uniform_length_unpeel.
    erewrite overlap_length, !peel_signals_length by eauto.
    lia.
  Qed.

  Lemma overlap_signals_pair {A B} offset (a1 a2 : @signals seqType _ (ipair A B)) n1 n2 :
    uniform_length n1 a1 -> uniform_length n2 a2 ->
    overlap_signals offset a1 a2 = (overlap_signals offset (fst a1) (fst a2),
                                    overlap_signals offset (snd a1) (snd a2)).
  Proof.
    intros; cbv [overlap_signals overlap].
    cbn [unpeel_signals peel_signals uniform_length] in *.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat destruct_pair_let. cbn [fst snd].
    autorewrite with push_split. cbn [fst snd].
    rewrite !combine_split by (erewrite !peel_signals_length by eauto; length_hammer).
    cbn [fst snd]. cbn [signals signals_gen].
    rewrite combine_length.
    erewrite !peel_signals_length by eauto.
    autorewrite with natsimpl. reflexivity.
  Qed.
End Overlap.
Hint Rewrite @overlap_cons1 @overlap_cons2 @overlap_nil_r @overlap_snoc_cons
     using solve [length_hammer] : seqsimpl.
Hint Rewrite @overlap_0_nil @overlap_app_same using solve [eauto] : seqsimpl.
Hint Rewrite @skipn_overlap_same @skipn_overlap_signals_same using solve [eauto] : push_skipn.

Section Loops.
  Existing Instance SequentialCombSemantics.
  Lemma loopSeqS'_step {A B}
        (f : signals A * signals B -> ident (signals B))
        (spec : @signals combType _ A -> @signals combType _ B
                -> signals B) :
    (forall a b, sequential (f (unpeel_signals [a], unpeel_signals [b])) = spec a b) ->
    forall (loop_state : nat * ident (signals B)) a,
      loopSeqS' f loop_state a
      = let t := fst loop_state in
        let acc := unIdent (snd loop_state) in
        let feedback := match t with
                        | 0 => defaultSignals B
                        | S t' => nth t' (peel_signals acc) (defaultSignals B)
                        end in
        let r := spec a feedback in
        (S t, ret (overlap_signals t acc r)).
  Proof.
    cbv [sequential loopSeqS' SequentialSemantics]. intro Hfspec.
    intros. seqsimpl. rewrite Hfspec. reflexivity.
  Qed.

  Lemma loopDelayS_stepwise {A B}
        (f : signals A * signals B -> ident (signals B))
        (spec : @signals combType _ A -> @signals combType _ B -> signals B)
        input :
    (forall a b, sequential (f (unpeel_signals [a], unpeel_signals [b])) = spec a b) ->
    sequential (loopDelayS (CavaSeq:=SequentialSemantics) f input)
    = snd (fold_left (fun loop_state a =>
                        let '(t, acc) := loop_state in
                        let feedback := match t with
                                        | 0 => defaultSignals B
                                        | S t' => nth t' (peel_signals acc) (defaultSignals B)
                                        end in
                        let r := spec a feedback in
                        (S t, overlap_signals t acc r))
                     (peel_signals input) (0, unpeel_signals [])).
  Proof.
    cbv [loopDelayS loopSeqS SequentialSemantics sequential]; intros.
    seqsimpl.
    erewrite fold_left_ext with (f0:=loopSeqS' _) by (apply loopSeqS'_step; eassumption).
    factor_out_loops.
    eapply fold_left_double_invariant
      with(I:=fun (x : nat * signals B) (y : nat * ident (signals B)) =>
                x = (fst y, unIdent (snd y))).
    { (* invariant holds at start *)
      reflexivity. }
    { (* invariant holds through loop *)
      intros; repeat destruct_pair_let. subst.
      seqsimpl. reflexivity. }
  { (* invariant implies postcondition *)
    intros. subst. seqsimpl. reflexivity. }
  Qed.

  Lemma loopDelayS_stepwise_indexed {A B}
        (f : signals A * signals B -> ident (signals B))
        (spec : @signals combType _ A -> @signals combType _ B -> signals B)
        input :
    (forall a b, sequential (f (unpeel_signals [a], unpeel_signals [b])) = spec a b) ->
    sequential (loopDelayS (CavaSeq:=SequentialSemantics) f input)
    = fold_left (fun acc t =>
                   let a := nth t (peel_signals input) (defaultSignals A) in
                   let feedback := match t with
                                   | 0 => defaultSignals B
                                   | S t' => nth t' (peel_signals acc) (defaultSignals B)
                                   end in
                   let r := spec a feedback in
                   overlap_signals t acc r)
                (seq 0 (length (peel_signals input))) (unpeel_signals []).
  Proof.
    intros. erewrite loopDelayS_stepwise by eassumption.
    erewrite fold_left_to_seq with (ls:=peel_signals input) (default:=defaultSignals A).
    pose (R:=fun t (x : signals B) (y : nat * signals B) => y  = (t, x)).
    factor_out_loops.
    lazymatch goal with
    | |- ?P ?loop1 ?loop2 =>
      let H := fresh in
      assert (R (length (peel_signals input)) loop1 loop2) as H;
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

  Lemma loopDelayS_invariant {A B}
        (I : nat -> signals B  -> Prop)
        (f : signals A * signals B -> ident (signals B))
        (P : signals B -> Prop) input :
    (* invariant is true for start state *)
    I 0 (unpeel_signals []) ->
    (* invariant holds through loop *)
    (forall t acc,
        I t acc ->
        t < length (peel_signals input) ->
        let a := nth t (peel_signals input) (defaultSignals A) in
        let feedback := match t with
                        | 0 => defaultSignals B
                        | S t' => nth t' (peel_signals acc) (defaultSignals B)
                        end in
        let r := sequential (f (unpeel_signals [a], unpeel_signals [feedback])) in
        I (S t) (overlap_signals t acc r)) ->
    (* invariant is strong enough to prove postcondition *)
    (forall b, I (length (peel_signals input)) b -> P b) ->
    P (sequential (loopDelayS (CavaSeq:=SequentialSemantics) f input)).
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
        (I : nat -> signals B -> Prop)
        (f : signals A * signals B -> ident (signals B))
        (P : signals B -> Prop) n input :
    (forall a b, uniform_length n (sequential (f (unpeel_signals [a], unpeel_signals [b])))) ->
    (* Either the input is nil and P holds on nil, or the invariant is satisfied
       after one step *)
    (match peel_signals input with
     | [] => P (unpeel_signals [])
     | i0 :: _ =>
       I 1 (sequential (f (unpeel_signals [i0],
                           unpeel_signals [defaultSignals B])))
     end) ->
    (* invariant holds through loop *)
    (forall t acc,
        I t acc ->
        0 < t < length (peel_signals input) ->
        let a := nth t (peel_signals input) (defaultSignals A) in
        let feedback := match t with
                        | 0 => defaultSignals B
                        | S t' => nth t' (peel_signals acc) (defaultSignals B)
                        end in
        let r := sequential (f (unpeel_signals [a], unpeel_signals [feedback])) in
        I (S t) (overlap_signals t acc r)) ->
    (* invariant is strong enough to prove postcondition *)
    (forall b, I (length (peel_signals input)) b -> P b) ->
    P (sequential (loopDelayS (CavaSeq:=SequentialSemantics) f input)).
  Proof.
    intros ? Hstart Hbody Hpost.
    erewrite loopDelayS_stepwise_indexed by (intros; reflexivity).
    destr (peel_signals input); [ cbn [fold_left]; seqsimpl; assumption | ].
    cbn [fold_left seq length]. seqsimpl.
    eapply fold_left_invariant_seq with (I0:=I).
    { cbv [overlap_signals]. rewrite peel_unpeel_signals.
      seqsimpl. erewrite unpeel_peel_signals by eauto.
      apply Hstart. }
    { intros *; repeat destruct_pair_let; intros.
      apply Hbody; eauto using in_cons; length_hammer. }
    { intros *; repeat destruct_pair_let; intros.
      eauto. }
  Qed.

  (* TODO(jadep) : ressurect these proofs
  Lemma loopDelay_invariant {A B C}
        (I : nat -> signals B -> signals C -> Prop)
        (f : signals A * signals C -> ident (signals B * signals C))
        (P : signals B -> Prop) n input :
    (* function produces same number of results for feedback and output *)
    (forall a b, uniform_length (A:=ipair B C) n
                           (sequential (f (unpeel_signals [a], unpeel_signals [b])))) ->
    (* invariant is true for start state *)
    I 0 (unpeel_signals []) (unpeel_signals []) ->
    (* invariant holds through loop *)
    (forall t b c,
        I t b c ->
        t < length (peel_signals input) ->
        let a := nth t (peel_signals input) (defaultSignals A) in
        let x := hd (defaultSignals C) (peel_signals c) in
        let r := sequential (f (unpeel_signals [a], unpeel_signals [x])) in
        let tl_c := unpeel_signals (tl (peel_signals c)) in
        I (S t) (overlap_signals t b (fst r))
          (overlap_signals 0 tl_c (snd r))) ->
    (* invariant is strong enough to prove postcondition *)
    (forall b c, I (length (peel_signals input)) b c -> P b) ->
    P (sequential (loopDelay (seqsemantics:=SequentialSemantics) f input)).
  Proof.
    intros Hlen ? Hbody; intros; cbv [loopDelay sequential]. seqsimpl.
    eapply loopDelayS_invariant
      with (I0:=fun t (bc : signals (ipair B C)) =>
                  (t = 0 -> peel_signals bc = nil) /\
                  uniform_length (if t =? 0 then 0 else n + t) (fst bc) /\
                  uniform_length (if t =? 0 then 0 else n) (snd bc) /\
                  I t (fst bc) (match t with
                                | 0 => unpeel_signals []
                                | S t' => snd (unpeel_signals (skipn t' (peel_signals bc)))
                                end)).
    { ssplit; rewrite ?peel_unpeel_signals; [ reflexivity | | | assumption ];
        cbn [unpeel_signals Nat.eqb]; apply uniform_length_unpeel;
          length_hammer. }
    { cbv zeta; intros *. intros [Ht0 [? [? HI]]]. intros.
      split; [ congruence | ]. repeat destruct_pair_let.
      cbv [sequential]; seqsimpl. cbn [fst snd].
      autorewrite with push_skipn. cbv zeta in Hbody.
      specialize (Hbody _ _ _ ltac:(eassumption) ltac:(eassumption)).
      (* Some unfortunately specific and manual replaces to make invariant
         expressions match *)
      match goal with
      | H : context [f (?x, ?y1)] |- context [f (?x, ?y2)] =>
        replace y2 with y1
      end.
      2:{ destruct_one_match; autorewrite with push_skipn;
          [ rewrite peel_unpeel_signals; reflexivity | ].
          cbn [unpeel_signals]. repeat destruct_pair_let.
          cbn [defaultSignals fst snd]. rewrite peel_unpeel_signals.
          cbn [signals signals_gen].
          rewrite split_nth. cbn [fst snd].
          cbn [peel_signals]. rewrite split_skipn.
          cbn [split snd]. rewrite hd_skipn. reflexivity. }
      erewrite unpeel_peel_signals.
      2:{
        eapply uniform_length_overlap_signals; [ | solve [eauto] .. ].
        eapply uniform_length_unpeel. length_hammer. }
      erewrite overlap_signals_pair.
      2:{ split; eauto. 
      erewrite !overlap_signals_pair by first [ solve [eauto]
                                              | solve [split; eauto]
                                              | apply uniform_length_unpeel; reflexivity ].
      cbn [fst snd].
      match goal with |- context [S ?t =? 0] => destr (S t =? 0) end; [ congruence | ].
      match goal with
      | |- context [f (unpeel_signals [?x], unpeel_signals [?y])] =>
        specialize (Hlen x y); cbn [uniform_length] in Hlen; destruct Hlen
      end.
      ssplit.
      { eapply uniform_length_overlap_signals; eauto; [ ].
        destr (t =? 0); subst; [ lia | ].
        lia.
        match goal with
      match goal with
      | H : context [overlap_signals 0 ?x1 ?y] |- context [overlap_signals 0 ?x2 ?y] =>
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
       let r := sequential (f ([i0], [defaultCombValue C])) in
       I 1 (fst r) (snd r)
     end) ->
    (* invariant holds through loop *)
    (forall t b c,
        I t b c ->
        0 < t < length input ->
        let a := nth t input (defaultCombValue A) in
        let x := hd (defaultCombValue C) c in
        let r := sequential (f ([a], [x])) in
        I (S t) (overlap t b (fst r)) (overlap 0 (tl c) (snd r))) ->
    (* invariant is strong enough to prove postcondition *)
    (forall b c, I (length input) b c -> P b) ->
    P (sequential (loopDelay (seqsemantics:=SequentialSemantics) f input)).
  Proof.
    intros ? ? Hbody; intros; cbv [loopDelay sequential]. seqsimpl.
    eapply loopDelayS_invariant_alt
      with (I0:=fun t (bc : seqType (Pair B C)) =>
                  I t (fst (unpair bc)) (match t with
                                         | 0 => []
                                         | S t' => snd (unpair (skipn t' bc))
                                         end)).
    { destruct input; [ solve [auto] | ].
      repeat destruct_pair_let.
      cbv zeta in *. cbn [sequential unIdent].
      autorewrite with push_skipn.
      rewrite unpair_mkpair
        by (cbn [unpair split SequentialCombSemantics];
            destruct_one_match; cbn [fst snd]; auto).
      cbn [fst snd]. auto. }
    { cbv zeta; intros. repeat destruct_pair_let.
      cbv [sequential]; seqsimpl. rewrite unpair_skipn.
      rewrite !unpair_overlap_mkpair_r
        by (destruct t; cbn [unpair split SequentialCombSemantics];
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
   *)
End Loops.

Section Evaluation.
  Lemma sequential_compose {A B C}
        (f : A -> @cava _ SequentialCombSemantics B)
        (g : B -> @cava _ SequentialCombSemantics C) i :
    sequential ((f >=> g) i) = sequential (g (sequential (f i))).
  Proof. reflexivity. Qed.

  Lemma delayCorrect {A} (i : @signals seqType _ A) :
    sequential (delay i) = unpeel_signals (defaultSignals A :: peel_signals i).
  Proof. reflexivity. Qed.

  Lemma fork2Correct {A} (i : seqType A) :
    sequential (fork2 i) = (i, i).
  Proof. reflexivity. Qed.
End Evaluation.
Hint Rewrite @sequential_compose @delayCorrect @fork2Correct
     using solve [eauto] : seqsimpl.
