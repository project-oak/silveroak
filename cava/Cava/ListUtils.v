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
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Cava.NatUtils.
Import ListNotations.
Local Open Scope list_scope.

(* Generic rewrite database for common list simplifications *)
Hint Rewrite @app_nil_l @app_nil_r @last_last @rev_app_distr : listsimpl.

Section Length.
  Lemma nil_length {A} : @length A nil = 0.
  Proof. reflexivity. Qed.
  Lemma cons_length {A} x (ls : list A) : length (x :: ls) = S (length ls).
  Proof. reflexivity. Qed.
  Lemma length_pos_nonnil {A} (l : list A) :
    (0 < length l)%nat -> l <> nil.
  Proof. destruct l; cbn [length]; (Lia.lia || congruence). Qed.
  Lemma tl_length {A} (l : list A) : length (tl l) = length l - 1.
  Proof. destruct l; cbn [length tl]; lia. Qed.
End Length.

(* The push_length autorewrite database simplifies goals including [length] *)
Hint Rewrite @nil_length @cons_length @seq_length @repeat_length @rev_length
     @map_length @firstn_length @skipn_length @app_length @combine_length
     @tl_length
     using solve [eauto] : push_length.
Create HintDb length discriminated.
Ltac length_hammer :=
  autorewrite with push_length; eauto with length; lia.

(* The push_nth database simplifies goals including [nth] *)
Hint Rewrite @app_nth1 @app_nth2 @nth_overflow using length_hammer : push_nth.
Hint Rewrite @combine_nth using solve [length_hammer] : push_nth.
Hint Rewrite @seq_nth using lia : push_nth.


(* Miscellaneous proofs about lists *)
Section Misc.
  Lemma rev_seq_S start len :
    rev (seq start (S len)) = (start + len) :: rev (seq start len).
  Proof. rewrite seq_S, rev_app_distr; reflexivity. Qed.

  Lemma seq_snoc start len :
    seq start (S len) = seq start len ++ [start + len].
  Proof. rewrite seq_S. reflexivity. Qed.

  Lemma rev_eq_nil {A} (l : list A) : rev l = nil -> l = nil.
  Proof.
    destruct l; [ reflexivity | ].
    cbn [rev]. intro Hnil.
    apply app_eq_nil in Hnil; destruct Hnil.
    congruence.
  Qed.

  Lemma rev_eq_cons {A} x (l l' : list A) : rev l = (x :: l') -> l = rev l' ++ [x].
  Proof.
    revert x l'; induction l using rev_ind; cbn [rev]; [ congruence | ].
    intros *. intro Hrev.
    rewrite rev_app_distr in Hrev.
    cbn [rev app] in *. inversion Hrev; subst.
    rewrite rev_involutive. reflexivity.
  Qed.

  Lemma eta_list {A} (l : list A) d : 0 < length l -> l = hd d l :: tl l.
  Proof. destruct l; length_hammer. Qed.

  Lemma repeat_append {A} (x : A) n m :
    repeat x (n + m) = repeat x n ++ repeat x m.
  Proof.
    revert m; induction n; [ reflexivity | ].
    intros. cbn [Nat.add repeat]. rewrite <-app_comm_cons.
    rewrite IHn. reflexivity.
  Qed.

  Lemma repeat_S {A} (x : A) n :
   repeat x (S n) = x :: repeat x n.
  Proof. reflexivity. Qed.

  Lemma combine_append {A B} (la1 la2 : list A) (lb1 lb2 : list B) :
    length la1 = length lb1 ->
    combine (la1 ++ la2) (lb1 ++ lb2) = combine la1 lb1 ++ combine la2 lb2.
  Proof.
    revert la1 la2 lb1 lb2; induction la1; intros.
    { destruct lb1; [ reflexivity | cbn [length] in *; lia ]. }
    { destruct lb1; cbn [length] in *; [ lia | ].
      rewrite <-!app_comm_cons. cbn [combine].
      rewrite <-!app_comm_cons. rewrite IHla1 by lia.
      reflexivity. }
  Qed.

  Lemma in_combine_impl {A B} (a : A) (b : B) l1 l2 :
    In (a,b) (combine l1 l2) -> In a l1 /\ In b l2.
  Proof. eauto using in_combine_l, in_combine_r. Qed.

  Lemma tl_app {A} (l1 l2 : list A) :
    l1 <> nil -> tl (l1 ++ l2) = tl l1 ++ l2.
  Proof.
    intros; destruct l1; [ congruence | ].
    cbn [tl app]. reflexivity.
  Qed.
End Misc.
Hint Rewrite @seq_snoc using solve [eauto] : pull_snoc.

(* Definition and proofs of [extend], which pads a list to a specified length *)
Section Extend.
  Definition extend {A} (l : list A) (d : A) (n : nat) : list A :=
    l ++ repeat d (n - length l).

  Lemma extend_nil {A} (d : A) n : extend [] d n = repeat d n.
  Proof. cbv [extend]. autorewrite with push_length natsimpl. reflexivity. Qed.

  Lemma extend_cons_S {A} x0 x (d : A) n :
    extend (x0 :: x) d (S n) = x0 :: extend x d n.
  Proof.
    cbv [extend]. autorewrite with push_length natsimpl.
    rewrite <-app_comm_cons; reflexivity.
  Qed.

  Lemma extend_le {A} l (d : A) n : n <= length l -> extend l d n = l.
  Proof.
    cbv [extend]; intros.
    rewrite (proj2 (Nat.sub_0_le _ _)) by lia.
    cbn [repeat]; autorewrite with listsimpl.
    reflexivity.
  Qed.

  Lemma extend_to_match {A B} l1 l2 (a : A) (b : B) :
    length (extend l1 a (length l2)) = length (extend l2 b (length l1)).
  Proof.
    cbv [extend]; intros. autorewrite with push_length.
    destruct (Nat.min_dec (length l1) (length l2));
      autorewrite with natsimpl; lia.
  Qed.

  Lemma extend_length {A} (l : list A) a n:
    length (extend l a n) = Nat.max (length l) n.
  Proof.
    cbv [extend]. autorewrite with push_length natsimpl.
    lia.
  Qed.
End Extend.
Hint Rewrite @extend_length using solve [eauto] : push_length.
Hint Rewrite @extend_nil @extend_cons_S using solve [eauto] : push_extend.
Hint Rewrite @extend_le using solve [length_hammer] : push_extend.

Section Combine.
  Lemma combine_nil_r {A B} (la : list A) :
    @combine A B la [] = [].
  Proof. destruct la; reflexivity. Qed.

  Lemma combine_repeat_r {A B} (la : list A) (b : B) n :
    length la <= n ->
    combine la (repeat b n) = map (fun a => (a,b)) la.
  Proof.
    revert n; induction la; [ reflexivity | ].
    destruct n; [ length_hammer | ].
    cbn [combine length map repeat]; intros.
    rewrite IHla by lia; reflexivity.
  Qed.

  Lemma combine_repeat_l {A B} (lb : list B) (a : A) n :
    length lb <= n ->
    combine (repeat a n) lb = map (fun b => (a,b)) lb.
  Proof.
    revert n; induction lb;
      [ cbn [repeat]; intros; rewrite combine_nil_r; reflexivity | ].
    destruct n; [ length_hammer | ].
    cbn [combine length map repeat]; intros.
    rewrite IHlb by lia; reflexivity.
  Qed.

  Lemma combine_length {A B} (la : list A) (lb : list B) :
    length (combine la lb) = Nat.min (length la) (length lb).
  Proof.
    revert lb; induction la; [ reflexivity | ].
    destruct lb; [ reflexivity | ].
    cbn [combine length Nat.min]. rewrite IHla.
    lia.
  Qed.
End Combine.
Hint Rewrite @combine_length : push_length.

(* Proofs about [split] *)
Section Split.
  Lemma split_skipn {A B} n (l : list (A * B)) :
    split (skipn n l) = (skipn n (fst (split l)), skipn n (snd (split l))).
  Proof.
    revert l; induction n; destruct l; try reflexivity; [ | ];
      repeat match goal with
             | _ => progress cbn [skipn split fst snd]
             | |- context [match ?p with pair _ _ => _ end ] =>
               rewrite (surjective_pairing p)
             | _ => solve [auto]
             end.
  Qed.

  Lemma split_app {A B} (l1 l2 : list (A * B)) :
    split (l1 ++ l2) = (fst (split l1) ++ fst (split l2),
                        snd (split l1) ++ snd (split l2)).
  Proof.
    revert l2; induction l1; destruct l2;
      repeat first [ progress cbn [split fst snd]
                   | progress autorewrite with listsimpl
                   | rewrite <-app_comm_cons
                   | match goal with
                     | |- context [match ?p with pair _ _ => _ end] =>
                       rewrite (surjective_pairing p)
                     end
                   | rewrite IHl1; clear IHl1
                   | reflexivity ].
  Qed.

  Lemma split_repeat {A B} n (ab : A * B) :
    split (repeat ab n) = (repeat (fst ab) n, repeat (snd ab) n).
  Proof.
    induction n;
      repeat first [ progress cbn [split repeat fst snd]
                   | match goal with
                     | |- context [match ?p with pair _ _ => _ end] =>
                       rewrite (surjective_pairing p)
                     end
                   | rewrite IHn
                   | rewrite <-surjective_pairing
                   | reflexivity ].
  Qed.

  Lemma split_map {A B} (l : list (A * B)) :
    split l = (map fst l, map snd l).
  Proof.
    induction l as [| [? ?] ?]; [ reflexivity | ].
    cbn [map split]. rewrite IHl. reflexivity.
  Qed.
End Split.
Hint Rewrite @split_skipn @split_app @split_repeat
     using solve [eauto] : push_split.

Section Nth.
  Lemma nth_step {A} n (l : list A) x d :
    nth (S n) (x :: l) d = nth n l d.
  Proof. reflexivity. Qed.

  Lemma nth_found {A} (l : list A) x d :
    nth 0 (x :: l) d = x.
  Proof. reflexivity. Qed.

  Lemma nth_nil {A} n (d : A) :
    nth n [] d = d.
  Proof. destruct n; reflexivity. Qed.

  Lemma nth_map_seq {T} (f : nat -> T) n start len d :
    n < len ->
    nth n (map f (seq start len)) d = f (start + n)%nat.
  Proof.
    revert n start; induction len; [ lia | ].
    intros; destruct n; cbn [seq map nth];
      autorewrite with natsimpl; [ reflexivity | ].
    rewrite IHlen by lia.
    f_equal; lia.
  Qed.

  Lemma map_nth_inbounds {A B} (f : A -> B) l d1 d2 n :
    n < length l -> nth n (map f l) d1 = f (nth n l d2).
  Proof.
    revert l; induction n; intros;
      (destruct l; autorewrite with push_length in *; [ lia | ]);
      [ reflexivity | ].
    cbn [map nth]. apply IHn. lia.
  Qed.

  Lemma nth_repeat_inbounds {A} (x : A) d n m :
    n < m -> nth n (repeat x m) d = x.
  Proof.
    revert m; induction n; destruct m; cbn [repeat nth]; intros;
      try apply IHn; lia || reflexivity.
  Qed.

  Lemma nth_repeat {A} (x : A) d n m :
    nth n (repeat x m) d = if n <? m then x else d.
  Proof.
    case_eq (n <? m); [ rewrite Nat.ltb_lt | rewrite Nat.ltb_nlt ]; intros;
      [ | rewrite nth_overflow by length_hammer; reflexivity ].
    apply nth_repeat_inbounds; lia.
  Qed.

  Lemma map_to_nth {A B} (f : A -> B) ls d :
    map f ls = map (fun i => f (nth i ls d)) (seq 0 (length ls)).
  Proof.
    induction ls; [ reflexivity | ].
    cbn [map length seq]. rewrite <-seq_shift, map_map.
    cbn [nth]. rewrite IHls; reflexivity.
  Qed.

  Lemma nth_inbounds_change_default {A} n (l : list A) (d1 d2 : A) :
    n < length l -> nth n l d1 = nth n l d2.
  Proof.
    revert l; induction n; (destruct l; [ length_hammer | ]); [ reflexivity | ].
    cbn [nth length]; intros. apply IHn. lia.
  Qed.

  Lemma nth_extend {A} (l : list A) a n i :
    nth i (extend l a n) a = nth i l a.
  Proof.
    cbv [extend]; destruct (Compare_dec.lt_dec i (length l));
      autorewrite with push_nth; [ reflexivity | ].
    rewrite nth_repeat, nth_overflow by lia.
    rewrite Tauto.if_same; reflexivity.
  Qed.

  Lemma nth_last {A} (l : list A) n d :
    n = length l - 1 ->
    nth n l d = last l d.
  Proof.
    revert n; induction l using rev_ind; intros; subst; [ reflexivity | ].
    autorewrite with push_length natsimpl listsimpl push_nth.
    reflexivity.
  Qed.

  Lemma Forall2_nth_iff {A B} (P : A -> B -> Prop) la lb :
    length la = length lb ->
    (forall i da db,
        0 <= i < length la ->
        P (nth i la da) (nth i lb db)) <->
    Forall2 P la lb.
  Proof.
    revert lb; induction la; destruct lb; intros;
      cbn [length] in *; try lia; [ | ].
    { split; [ solve [auto] | lia ]. }
    { split.
      { intro Hnth; constructor.
        { specialize (Hnth 0). cbn [nth] in Hnth.
          apply Hnth; auto; lia. }
        { apply IHla; [ lia | ].
          intro i; intros.
          specialize (Hnth (S i)).
          cbn [nth] in Hnth. apply Hnth; lia. } }
      { inversion 1; intros; subst.
        match goal with |- context [nth ?i] =>
                        destruct i end;
          cbn [nth]; auto; [ ].
        apply IHla; auto; lia. } }
  Qed.

  Lemma list_eq_elementwise {A} (l1 l2 : list A) :
    length l1 = length l2 ->
    (forall i d, 0 <= i < length l1 -> nth i l1 d = nth i l2 d) ->
    l1 = l2.
  Proof.
    revert l2; induction l1; destruct l2; try length_hammer; [ ].
    cbn [length]; intros ? Hnth. pose proof Hnth as Hnth0.
    specialize (Hnth0 0). cbn [nth] in Hnth0.
    rewrite Hnth0 by (auto; lia). f_equal; [ ].
    apply IHl1; [ length_hammer | ].
    intro i; intros. specialize (Hnth (S i)).
    cbn [nth] in Hnth. apply Hnth; lia.
  Qed.

  Lemma nth_tl {A} n (l : list A) d : nth n (tl l) d = nth (S n) l d.
  Proof. destruct l; destruct n; reflexivity. Qed.
End Nth.
Hint Rewrite @nth_step @nth_found @nth_nil @nth_extend using solve [eauto] : push_nth.
Hint Rewrite @nth_map_seq @map_nth_inbounds @nth_repeat_inbounds
     using lia : push_nth.

Section Maps.
  Lemma map_id_ext {A} (f : A -> A) (l : list A) :
    (forall a, f a = a) -> map f l = l.
  Proof.
    intro Hf; induction l; [reflexivity|].
    simpl.
    rewrite Hf, IHl.
    reflexivity.
  Qed.

  Lemma map_snoc {A B} (f : A -> B) ls a :
    map f (ls ++ [a]) = map f ls ++ [f a].
  Proof. rewrite map_app. reflexivity. Qed.

  Lemma map_repeat {A B} (f : A -> B) a n :
    map f (repeat a n) = repeat (f a) n.
  Proof.
    induction n; [ reflexivity | ].
    cbn [repeat map]; rewrite IHn; reflexivity.
  Qed.

  Lemma map_constant {A B} (ls : list A) (b : B) :
    map (fun _ => b) ls = repeat b (length ls).
  Proof.
    induction ls; [ reflexivity | ].
    cbn [map length repeat]; congruence.
    Qed.

  Lemma flat_map_nil_ext {A B} (l : list A) :
    flat_map (B:=B) (fun a => []) l = [].
  Proof.
    induction l; [ reflexivity | ].
    cbn [flat_map]. rewrite IHl; reflexivity.
  Qed.

  Lemma combine_map_l {A B C} (f : A -> B) la (lc : list C) :
    combine (map f la) lc = map (fun ac => (f (fst ac), snd ac))
                                (combine la lc).
  Proof.
    revert lc; induction la; [ reflexivity | ].
    destruct lc; intros; [ reflexivity | ].
    cbn [map combine fst snd]. rewrite IHla.
    reflexivity.
  Qed.

  Lemma combine_map_r {A B C} (f : B -> C) (la : list A) lb :
    combine la (map f lb) = map (fun ab => (fst ab, f (snd ab)))
                                (combine la lb).
  Proof.
    revert lb; induction la; [ reflexivity | ].
    destruct lb; intros; [ reflexivity | ].
    cbn [map combine fst snd]. rewrite IHla.
    reflexivity.
  Qed.

  Lemma flat_map_map {A B C} (f : A -> B) (g : B -> list C) la :
    flat_map g (map f la) = flat_map (fun a => g (f a)) la.
  Proof.
    induction la; [ reflexivity | ].
    cbn [map flat_map]. rewrite IHla.
    reflexivity.
  Qed.

  Lemma map_flat_map {A B C} (f : A -> list B) (g : B -> C) la :
    map g (flat_map f la) = flat_map (fun a => map g (f a)) la.
  Proof.
    induction la; [ reflexivity | ].
    cbn [map flat_map]. rewrite map_app.
    rewrite IHla. reflexivity.
  Qed.

  Lemma flat_map_nonnil {A B} (f : A -> list B) la :
    la <> [] -> (forall a, f a <> nil) ->
    flat_map f la <> nil.
  Proof.
    intros ? Hf.
    destruct la as [|a ?]; intros; [ congruence | ].
    specialize (Hf a).
    cbn [flat_map]. intro Heq.
    apply app_eq_nil in Heq.
    tauto.
  Qed.

  Fixpoint map2 {A B C} (f : A -> B -> C) (ls1 : list A) ls2 :=
    match ls1, ls2 with
    | a :: ls1', b :: ls2' => f a b :: map2 f ls1' ls2'
    | _, _ => []
    end.

  Lemma map2_length A B C (f : A -> B -> C) (l1 : list A) (l2 : list B) :
    length (map2 f l1 l2) = Nat.min (length l1) (length l2).
  Proof.
    revert l2.
    induction l1; [reflexivity|].
    destruct l2; [reflexivity|].
    simpl.
    rewrite (IHl1 l2).
    reflexivity.
  Qed.

  Lemma map2_ext {A B C} (f g : A -> B -> C) (la : list A) lb :
      (forall a b, f a b = g a b) -> map2 f la lb = map2 g la lb.
  Proof.
    intros.
    revert lb.
    induction la; [reflexivity|].
    intros.
    destruct lb; [reflexivity|].
    simpl.
    rewrite (H a b).
    rewrite IHla.
    reflexivity.
  Qed.

  Lemma in_map2_impl {A B C} (f : A -> B -> C) (la : list A) lb c :
    In c (map2 f la lb) -> (exists a b, f a b = c /\ In a la /\ In b lb).
  Proof.
    revert lb; induction la; destruct lb; cbn [map2 In];
      [ tauto .. | ].
    intros [? | ?];
      [ subst; do 2 eexists; repeat split; tauto | ].
    specialize (IHla _ ltac:(eassumption)).
    destruct IHla as [? [? [? [? ?]]]]. subst.
    do 2 eexists; eauto.
  Qed.

  Lemma map2_id_l {A B} (l1 : list A) (l2 : list B) (HL : length l2 >= length l1) : map2 (fun a _ => a) l1 l2 = l1.
  Proof.
    generalize dependent l2.
    induction l1; [reflexivity|].
    intros.
    destruct l2; [inversion HL|].
    simpl.
    rewrite IHl1.
    { reflexivity. }
    { simpl in HL.
      inversion HL; lia. }
  Qed.

  Lemma map2_map2_r {A B C D} (f : A -> B -> C) (g : C -> B -> D) (ls1 : list A) ls2 :
    map2 g (map2 f ls1 ls2) ls2 = map2 (fun a b => g (f a b) b) ls1 ls2.
  Proof.
    revert ls2.
    induction ls1; [reflexivity|].
    intros.
    destruct ls2; [reflexivity|].
    simpl.
    rewrite IHls1.
    reflexivity.
  Qed.

  Lemma map2_swap {A B C} (f : A -> B -> C) la lb :
    map2 f la lb = map2 (fun b a => f a b) lb la.
  Proof.
    revert lb; induction la; destruct lb; cbn [map2];
      [ reflexivity .. | ].
    rewrite IHla; reflexivity.
  Qed.

  Lemma map2_app {A B C} (f : A -> B -> C) la1 la2 lb1 lb2 :
    length la1 = length lb1 ->
    map2 f (la1 ++ la2) (lb1 ++ lb2) = map2 f la1 lb1 ++ map2 f la2 lb2.
  Proof.
    revert la1 la2 lb1 lb2.
    induction la1; destruct lb1; cbn [length]; [ reflexivity | congruence .. | ].
    intros. rewrite <-!app_comm_cons. cbn [map2].
    rewrite <-app_comm_cons, IHla1 by Lia.lia.
    reflexivity.
  Qed.

  Lemma map2_drop_same {A B} (f : A -> A -> B) la :
    map2 f la la = map (fun a => f a a) la.
  Proof.
    induction la; [ reflexivity | ].
    cbn [map2]; rewrite IHla; reflexivity.
  Qed.
End Maps.
Hint Rewrite @map2_length using solve [eauto] : push_length.
Hint Rewrite @map_snoc using solve [eauto] : pull_snoc.

(* Proofs about firstn and skipn *)
Section FirstnSkipn.
  Lemma skipn_skipn {A} n m (x : list A) :
    skipn n (skipn m x) = skipn (n + m) x.
  Proof.
    revert n x; induction m; intros; [ f_equal; lia | ].
    rewrite Nat.add_succ_r.
    cbn [skipn]. destruct x; [ rewrite skipn_nil; reflexivity |].
    apply IHm.
  Qed.

  Lemma skipn_repeat {A} n (x : A) m :
    skipn n (repeat x m) = repeat x (m - n).
  Proof.
    revert n x; induction m; intros; [ rewrite skipn_nil; reflexivity | ].
    destruct n; autorewrite with natsimpl; [ reflexivity | ].
    cbn [repeat skipn].
    rewrite IHm; reflexivity.
  Qed.

  Lemma firstn_succ_snoc {A} (x : list A) n d :
    n < length x ->
    firstn (S n) x = firstn n x ++ [nth n x d].
  Proof.
    revert x; induction n.
    { destruct x; cbn [length firstn nth]; intros;
        (reflexivity || lia). }
    { intros. destruct x; cbn [length] in *; [ lia | ].
      rewrite !firstn_cons. cbn [nth].
      rewrite IHn by lia.
      apply app_comm_cons. }
  Qed.

  Lemma hd_skipn {A} n (l : list A) d : hd d (skipn n l) = nth n l d.
  Proof.
    revert l; induction n; intros; [ destruct l; reflexivity | ].
    destruct l; [ reflexivity | ]. cbn [skipn nth].
    apply IHn.
  Qed.

  Lemma tl_skipn {A} n (l : list A) : tl (skipn n l) = skipn (S n) l.
  Proof.
    revert l; induction n; intros; [ destruct l; reflexivity | ].
    destruct l; [ reflexivity | ]. cbn [skipn tl].
    apply IHn.
  Qed.

  Lemma skipn_combine {A B} (la : list A) (lb : list B) n :
    skipn n (combine la lb) = combine (skipn n la) (skipn n lb).
  Proof.
    revert la lb; induction n; intros; [ reflexivity | ].
    destruct la; [ reflexivity | ].
    destruct lb; cbn [skipn combine]; [ rewrite combine_nil; reflexivity | ].
    rewrite IHn. reflexivity.
  Qed.
End FirstnSkipn.
Hint Rewrite @skipn_app @skipn_skipn @skipn_repeat @skipn_cons @skipn_O
     @skipn_nil @skipn_all @skipn_combine
     using solve [eauto] : push_skipn.
Hint Rewrite @firstn_nil @firstn_cons @firstn_all @firstn_app @firstn_O
     @firstn_firstn @combine_firstn
     using solve [eauto] : push_firstn.

(* Proofs about fold_right and fold_left *)
Section Folds.
  Lemma fold_left_nil {A B} (f : B -> A -> B) b :
    fold_left f [] b = b.
  Proof. reflexivity. Qed.

  Lemma fold_left_cons {A B} (f : B -> A -> B) b a ls :
    fold_left f (a::ls) b = fold_left f ls (f b a).
  Proof. reflexivity. Qed.

  Lemma fold_left_assoc {A} (f : A -> A -> A) id
        (right_identity : forall a, f a id = a)
        (left_identity : forall a, f id a = a)
        (associative :
           forall a b c, f a (f b c) = f (f a b) c) :
    forall l start,
      fold_left f l start = f start (fold_left f l id).
  Proof.
    induction l; cbn [fold_left]; intros.
    { rewrite right_identity. reflexivity. }
    { rewrite left_identity.
      rewrite IHl, <-associative, <-IHl.
      reflexivity. }
  Qed.

  Lemma fold_left_ext_In {A B} (f g : B -> A -> B) b ls :
    (forall b a, In a ls -> f b a = g b a) ->
    fold_left f ls b = fold_left g ls b.
  Proof.
    intro Hfg.
    revert b; induction ls; cbn [fold_left]; [ reflexivity | ].
    intros. rewrite IHls by auto using in_cons.
    rewrite Hfg; eauto using in_eq.
  Qed.

  Lemma fold_left_ext {A B} (f g : B -> A -> B) b ls :
    (forall b a, f b a = g b a) ->
    fold_left f ls b = fold_left g ls b.
  Proof.
    revert b; induction ls; intros; [ reflexivity | ].
    cbn [fold_left]; rewrite IHls by auto.
    congruence.
  Qed.

  Lemma fold_left_preserves_relation {A B C}
        (R : B -> C -> Prop) (f : B -> A -> B) (g : C -> A -> C) :
    forall ls b c,
      R b c ->
      (forall b c a, R b c -> R (f b a) (g c a)) ->
      R (fold_left f ls b) (fold_left g ls c).
  Proof.
    induction ls; intros; [ eassumption | ].
    cbn [fold_left]. eauto.
  Qed.

  Lemma fold_left_preserves_relation_seq {B C}
        (R : nat -> B -> C -> Prop) (f : B -> nat -> B) (g : C -> nat -> C) :
    forall len start b c,
      R start b c ->
      (forall b c n,
          start <= n < start + len ->
          R n b c -> R (S n) (f b n) (g c n)) ->
      R (start + len)
        (fold_left f (List.seq start len) b)
        (fold_left g (List.seq start len) c).
  Proof.
    induction len; intros;
      [ rewrite Nat.add_0_r; eassumption | ].
    cbn [List.seq fold_left].
    rewrite <-Nat.add_succ_comm.
    assert (start <= start < start + S len) by lia.
    assert (forall n, S start <= n < S start + len ->
                 start <= n < start + S len) by lia.
    eauto.
  Qed.

  Lemma fold_left_map {A B C}
        (f : C -> B -> C) (g : A -> B) ls c :
    fold_left f (map g ls) c = fold_left (fun c a => f c (g a)) ls c.
  Proof.
    revert c.
    induction ls; intros; [ reflexivity | ].
    cbn [fold_left map].
    rewrite IHls. reflexivity.
  Qed.

  Lemma fold_left_to_seq {A B} (f : A -> B -> A) ls b default :
    fold_left f ls b = fold_left (fun b i =>
                                    f b (nth i ls default))
                                 (seq 0 (length ls)) b.
  Proof.
    revert b. induction ls; intros; [ reflexivity | ].
    cbn [fold_left length seq]. rewrite IHls.
    rewrite <-seq_shift, fold_left_map.
    eapply fold_left_ext_In; intros *.
    rewrite in_seq; intros.
    reflexivity.
  Qed.

  Lemma fold_left_snoc {A B} (f : A -> B -> A) ls a b :
    fold_left f (ls ++ [b]) a = f (fold_left f ls a) b.
  Proof. rewrite fold_left_app. reflexivity. Qed.

  Lemma fold_left_invariant {A B} (I P : B -> Prop)
        (f : B -> A -> B) (ls : list A) b :
    I b -> (* invariant holds at start *)
    (forall b a, I b -> In a ls -> I (f b a)) -> (* invariant holds through loop body *)
    (forall b, I b -> P b) -> (* invariant implies postcondition *)
    P (fold_left f ls b).
  Proof.
    intros ? ? IimpliesP. apply IimpliesP. clear IimpliesP P.
    revert dependent b. revert dependent ls.
    induction ls; intros; cbn [fold_left]; [ assumption | ].
    apply IHls; intros; auto using in_cons, in_eq.
  Qed.

  Lemma fold_left_invariant_seq {A} (I : nat -> A -> Prop) (P : A -> Prop)
        (f : A -> nat -> A) start len a :
    I start a -> (* invariant holds at start *)
    (forall n a, I n a -> start <= n < start + len ->
            I (S n) (f a n)) -> (* invariant holds through loop body *)
    (forall a, I (start + len) a -> P a) -> (* invariant implies postcondition *)
    P (fold_left f (seq start len) a).
  Proof.
    intros Istart Ibody IimpliesP. apply IimpliesP. clear IimpliesP P.
    revert dependent a. revert dependent start. revert dependent len.
    induction len; intros; cbn [fold_left].
    { autorewrite with natsimpl. cbn [seq fold_left].
      apply Istart. }
    { rewrite seq_S, fold_left_app. cbn [fold_left].
      rewrite Nat.add_succ_r. apply Ibody; [ | lia ].
      apply IHlen; auto; [ ].
      intros. apply Ibody; eauto; lia. }
  Qed.

  (* Uses an invariant to relate two loops to each other *)
  Lemma fold_left_double_invariant {A B C} (I P : B -> C -> Prop)
        (f : B -> A -> B) (g : C -> A -> C) (ls : list A) b c :
    I b c -> (* invariant holds at start *)
    (forall b c a, I b c -> I (f b a) (g c a)) -> (* invariant holds through loop body *)
    (forall b c, I b c -> P b c) -> (* invariant implies postcondition *)
    P (fold_left f ls b) (fold_left g ls c).
  Proof.
    intros ? ? IimpliesP. apply IimpliesP.
    apply fold_left_preserves_relation; eauto.
  Qed.

  (* Similar to fold_left_double_invariant, except the invariant can depend on
     the index *)
  Lemma fold_left_double_invariant_seq {A B}
        (I : nat -> A -> B -> Prop) (P : A -> B -> Prop)
        (f : A -> nat -> A) (g : B -> nat -> B) start len a b :
    I start a b -> (* invariant holds at start *)
    (forall i a b, I i a b -> start <= i < start + len ->
              I (S i) (f a i) (g b i)) -> (* invariant holds through loop body *)
    (forall a b, I (start + len) a b -> P a b) -> (* invariant implies postcondition *)
    P (fold_left f (seq start len) a) (fold_left g (seq start len) b).
  Proof.
    intros ? ? IimpliesP. apply IimpliesP.
    apply fold_left_preserves_relation_seq; eauto.
  Qed.
End Folds.
Hint Rewrite @fold_left_cons @fold_left_nil @fold_left_app
     using solve [eauto] : push_list_fold.
Hint Rewrite @fold_left_snoc using solve [eauto] : pull_snoc.

(* Defines a version of fold_left that accumulates a list of (a
   projection of) all the states it passed through *)
Section FoldLeftAccumulate.
  Definition fold_left_accumulate' {A B}
             (f : B -> A -> B) acc0 ls b : list B * B :=
    fold_left (fun '(acc, b) a => (acc ++ [f b a], f b a))
              ls (acc0 ++ [b], b).
  Definition fold_left_accumulate {A B} (f : B -> A -> B) :=
    fold_left_accumulate' f nil.

  Lemma fold_left_accumulate'_nil {A B}
        (f : B -> A -> B) b acc0 :
    fst (fold_left_accumulate' f acc0 [] b) = (acc0 ++ [b]).
  Proof. reflexivity. Qed.

  Hint Rewrite @fold_left_accumulate'_nil : push_fold_acc.

  Lemma fold_left_accumulate'_cons {A B}
        (f : B -> A -> B) b a acc0 ls :
    fst (fold_left_accumulate' f acc0 (a::ls) b)
    = fst (fold_left_accumulate' f (acc0 ++ [b]) ls (f b a)).
  Proof. reflexivity. Qed.

  Hint Rewrite @fold_left_accumulate'_cons : push_fold_acc.

  Lemma fold_left_accumulate'_snd {A B} (f : B -> A -> B) :
    forall ls acc0 b,
      snd (fold_left_accumulate' f acc0 ls b) = fold_left f ls b.
  Proof.
    cbv [fold_left_accumulate'].
    induction ls; intros; [ reflexivity | ].
    cbn [fold_left]. erewrite <-IHls.
    reflexivity.
  Qed.

  Lemma fold_left_accumulate'_cons_full {A B}
        (f : B -> A -> B) b a acc0 ls :
    fold_left_accumulate' f acc0 (a::ls) b
    = (fst (fold_left_accumulate'
              f (acc0 ++ [b]) ls (f b a)),
       snd (fold_left_accumulate'
              f (acc0 ++ [b]) ls (f b a))).
  Proof.
    rewrite <-surjective_pairing; reflexivity.
  Qed.

  Lemma fold_left_accumulate'_equiv {A B}
        (f : B -> A -> B) b acc0 ls :
    fst (fold_left_accumulate' f acc0 ls b)
    = (acc0 ++ fst (fold_left_accumulate' f [] ls b)).
  Proof.
    revert acc0 b.
    induction ls; intros; autorewrite with push_fold_acc listsimpl;
      [ reflexivity | ].
    rewrite IHls with (acc0:=(_++_)).
    rewrite IHls with (acc0:=(_::_)).
    rewrite app_assoc_reverse.
    reflexivity.
  Qed.

  Lemma fold_left_accumulate'_snoc {A B}
        (f : B -> A -> B) b a acc0 ls :
    fst (fold_left_accumulate' f acc0 (ls ++ [a]) b)
    = let r := fold_left_accumulate' f acc0 ls b in
      (fst r ++ [f (snd r) a]).
  Proof.
    cbv zeta. revert acc0 b.
    induction ls; intros; rewrite <-?app_comm_cons;
      autorewrite with push_fold_acc listsimpl;
      [ reflexivity | ].
    rewrite IHls. reflexivity.
  Qed.

  Lemma fold_left_accumulate'_last {A B}
        (f : B -> A -> B) b d acc0 ls :
    last (fst (fold_left_accumulate' f acc0 ls b)) d = fold_left f ls b.
  Proof.
    revert acc0 b; induction ls; intros; cbn [fold_left];
      autorewrite with push_fold_acc; eauto using last_last.
  Qed.

  Lemma fold_left_accumulate'_length {A B} (f : B -> A -> B) :
    forall ls acc0 b,
      length (fst (fold_left_accumulate'
                     f acc0 ls b)) = length acc0 + S (length ls).
  Proof.
    induction ls; intros; autorewrite with push_fold_acc;
      rewrite ?IHls; length_hammer.
  Qed.

  Lemma fold_left_accumulate'_ext1_In {A B}
        (f1 f2 : B -> A -> B) ls acc0 b
        (Hext : forall b a, In a ls -> f1 b a = f2 b a) :
    fold_left_accumulate' f1 acc0 ls b
    = fold_left_accumulate' f2 acc0 ls b.
  Proof.
    cbv [fold_left_accumulate']; intros.
    apply fold_left_ext_In; intros.
    repeat match goal with
           | x : _ * _ |- _ => destruct x end.
    rewrite Hext by auto; reflexivity.
  Qed.

  Lemma fold_left_accumulate'_ext1 {A B}
        (f1 f2 : B -> A -> B) (Hext : forall b a, f1 b a = f2 b a)
        ls acc0 b :
    fold_left_accumulate' f1 acc0 ls b
    = fold_left_accumulate' f2 acc0 ls b.
  Proof.
    eauto using fold_left_accumulate'_ext1_In.
  Qed.

  Lemma fold_left_accumulate_nil {A B} (f : B -> A -> B) b :
    fst (fold_left_accumulate f [] b) = [b].
  Proof. reflexivity. Qed.

  Lemma fold_left_accumulate_cons {A B} (f : B -> A -> B) b a ls :
    fst (fold_left_accumulate f (a::ls) b)
    = (b :: fst (fold_left_accumulate f ls (f b a))).
  Proof.
    cbv [fold_left_accumulate].
    autorewrite with push_fold_acc listsimpl.
    rewrite fold_left_accumulate'_equiv.
    reflexivity.
  Qed.

  Lemma fold_left_accumulate_snd {A B} (f : B -> A -> B) :
    forall ls b,
      snd (fold_left_accumulate f ls b) = fold_left f ls b.
  Proof. intros; apply fold_left_accumulate'_snd. Qed.

  Lemma fold_left_accumulate_cons_full {A B}
        (f : B -> A -> B) b a ls :
    fold_left_accumulate f (a::ls) b
    = (b :: fst (fold_left_accumulate f ls (f b a)),
       snd (fold_left_accumulate f ls (f b a))).
  Proof.
    rewrite (surjective_pairing (fold_left_accumulate _ (_ :: _) _)).
    rewrite fold_left_accumulate_cons, !fold_left_accumulate_snd.
    reflexivity.
  Qed.

  Lemma fold_left_accumulate_snoc {A B} (f : B -> A -> B) b a ls :
    fst (fold_left_accumulate f (ls ++ [a]) b)
    = let r := fold_left_accumulate f ls b in
      fst r ++ [f (snd r) a].
  Proof.
    cbv [fold_left_accumulate].
    rewrite fold_left_accumulate'_snoc.
    reflexivity.
  Qed.

  Lemma fold_left_accumulate_last {A B} (f : B -> A -> B) b c ls :
    last (fst (fold_left_accumulate f ls b)) c = fold_left f ls b.
  Proof.
    cbv [fold_left_accumulate]. apply fold_left_accumulate'_last.
  Qed.

  Lemma fold_left_accumulate_length {A B} (f : B -> A -> B) ls b :
    length (fst (fold_left_accumulate f ls b)) = S (length ls).
  Proof.
    cbv [fold_left_accumulate].
    rewrite fold_left_accumulate'_length.
    reflexivity.
  Qed.

  Lemma fold_left_accumulate_ext_In {A B} (f1 f2 : B -> A -> B) ls b
        (Hext : forall b a, In a ls -> f1 b a = f2 b a) :
    fold_left_accumulate f1 ls b = fold_left_accumulate f2 ls b.
  Proof.
    cbv [fold_left_accumulate]; intros.
    auto using fold_left_accumulate'_ext1_In.
  Qed.

  Lemma fold_left_accumulate_ext {A B}
        (f1 f2 : B -> A -> B) (Hext : forall b a, f1 b a = f2 b a)
        ls b :
    fold_left_accumulate f1 ls b = fold_left_accumulate f2 ls b.
  Proof. eauto using fold_left_accumulate_ext_In. Qed.

  Lemma fold_left_accumulate_map {A B C}
        (f : C -> B -> C) (g : A -> B) ls b :
    fold_left_accumulate f (map g ls) b =
    fold_left_accumulate (fun b a => f b (g a)) ls b.
  Proof.
    revert b.
    induction ls; intros; [ reflexivity | ].
    rewrite map_cons, !fold_left_accumulate_cons_full.
    rewrite IHls. reflexivity.
  Qed.

  Lemma fold_left_fold_left_accumulate {A B C}
        (f : B -> A -> B) (g : C -> B -> C) :
    forall ls b c,
      fold_left
        g (fst (fold_left_accumulate f ls b)) c =
      snd (fold_left
             (fun '(b,c) a => (f b a, g c (f b a)))
             ls (b, g c b)).
  Proof.
    induction ls; intros; [ reflexivity | ].
    rewrite fold_left_accumulate_cons.
    cbn [fold_left]. rewrite IHls.
    reflexivity.
  Qed.

  Lemma nth_fold_left_accumulate' {A B}
        (f : B -> A -> B) :
    forall ls acc0 b d i,
      length acc0 <= i <= length acc0 + length ls ->
      nth i (fst (fold_left_accumulate' f acc0 ls b)) d =
      fold_left f (firstn (i-length acc0) ls) b.
  Proof.
    induction ls; cbn [length]; intros.
    { rewrite firstn_all2 by (cbn [length]; lia).
      cbn [fold_left_accumulate' fold_left fst].
      rewrite app_nth2 by lia.
      replace (i-length acc0) with 0 by lia.
      reflexivity. }
    { rewrite fold_left_accumulate'_cons.
      destruct (Nat.eq_dec (length acc0) i).
      { subst. rewrite fold_left_accumulate'_equiv.
        rewrite app_nth1, app_nth2 by length_hammer.
        rewrite Nat.sub_diag; reflexivity. }
      { rewrite IHls by length_hammer.
        rewrite <-(Nat.succ_pred_pos (i-length acc0)) by lia.
        autorewrite with push_length. rewrite Nat.add_1_r.
        cbn [fold_left firstn]. repeat (f_equal; [ ]).
        lia. } }
  Qed.

  Lemma nth_fold_left_accumulate {A B}
        (f : B -> A -> B) :
    forall ls b d i,
      i <= length ls ->
      nth i (fst (fold_left_accumulate f ls b)) d =
      fold_left f (firstn i ls) b.
  Proof.
    cbv [fold_left_accumulate]; intros.
    rewrite nth_fold_left_accumulate' by (cbn [length]; lia).
    rewrite Nat.sub_0_r. reflexivity.
  Qed.

  Lemma fold_left_accumulate_to_seq
        {A B} (f : A -> B -> A) ls b default :
    fold_left_accumulate f ls b =
    fold_left_accumulate
      (fun x i => f x (nth i ls default)) (seq 0 (length ls)) b.
  Proof.
    cbv [fold_left_accumulate fold_left_accumulate'].
    rewrite fold_left_to_seq with (default0:=default).
    apply fold_left_ext; intros [? ?] ?.
    reflexivity.
  Qed.

  Lemma fold_left_accumulate_double_invariant_seq {A B}
        (I : nat -> A -> B -> Prop) (P : list A * A -> list B * B -> Prop)
        (f : A -> nat -> A) (g : B -> nat -> B) start len a b :
    I start a b -> (* invariant holds at start *)
    (* invariant holds through loop body *)
    (forall i a b, I i a b -> start <= i < start + len ->
              I (S i) (f a i) (g b i)) ->
    (* invariant implies postcondition *)
    (forall a b acc1 acc2,
        I (start + len) a b ->
        (forall i da db,
            start <= i <= start + len ->
            I i (nth (i - start) acc1 da)
              (nth (i - start) acc2 db)) ->
        length acc1 = S len ->
        length acc2 = S len ->
        P (acc1, a) (acc2, b)) ->
    P (fold_left_accumulate f (seq start len) a)
      (fold_left_accumulate g (seq start len) b).
  Proof.
    intros ? ? IimpliesP. cbv [fold_left_accumulate fold_left_accumulate'].
    eapply fold_left_double_invariant_seq
      with (I0 := fun i '(acc1, a') '(acc2, b') =>
                    (forall j d1 d2,
                        start <= j <= i ->
                        I j
                          (nth (j - start) acc1 d1)
                          (nth (j - start) acc2 d2))
                    /\ I i a' b'
                    /\ last acc1 a = a'
                    /\ last acc2 b = b'
                    /\ length acc1 = S i - start
                    /\ length acc2 = S i - start);
      intros;
      repeat match goal with
             | x : _ * _ |- _ => destruct x
             | H : _ /\ _ |- _ => destruct H
             | |- _ /\ _ => split; try length_hammer
             | |- last _ _ = _ => apply last_last
             end.
    { intros j; intros. assert (j = start) by lia; subst.
      autorewrite with natsimpl push_nth.
      assumption. }
    { intros j ? ? [? jupper].
      apply Lt.le_lt_or_eq in jupper.
      destruct jupper; subst;
        [ assert (start <= j <= i) by lia | ];
        autorewrite with natsimpl push_nth; auto. }
    { subst; auto.
      apply IimpliesP; length_hammer. }
  Qed.

  (* Uses an invariant to relate two loops to each other *)
  Lemma fold_left_accumulate_double_invariant {A B C}
        (I : B -> C -> Prop) (P : (list B * B) -> (list C * C) -> Prop)
        (f1 : B -> A -> B) (f2 : C -> A -> C)
        (ls : list A) b d :
    I b d -> (* invariant holds at start *)
    (forall b d a, I b d -> I (f1 b a) (f2 d a)) -> (* invariant holds through loop body *)
    (* invariant implies postcondition *)
    (forall b d acc1 acc2,
        I b d ->
        Forall2 I acc1 acc2 ->
        P (acc1, b) (acc2, d)) ->
    P (fold_left_accumulate f1 ls b)
      (fold_left_accumulate f2 ls d).
  Proof.
    intros ? ? IimpliesP. cbv [fold_left_accumulate fold_left_accumulate'].
    eapply fold_left_double_invariant
      with (I0 := fun '(acc1, a') '(acc2, b') =>
                    Forall2 I acc1 acc2
                    /\ I a' b');
      intros;
      repeat match goal with
             | x : _ * _ |- _ => destruct x
             | H : _ /\ _ |- _ => destruct H
             | |- _ /\ _ => split; try length_hammer
             | |- last _ _ = _ => apply last_last
             end.
    { cbn [app]; repeat constructor; auto. }
    { apply Forall2_app; auto. }
    { apply IimpliesP; auto. }
  Qed.

End FoldLeftAccumulate.

Hint Rewrite @fold_left_accumulate_cons @fold_left_accumulate_nil
     using solve [eauto] : push_fold_acc.
Hint Rewrite @fold_left_accumulate'_length @fold_left_accumulate_length
     using solve [eauto] : push_length.

Ltac destruct_lists_by_length :=
  repeat
    match goal with
    | H : length ?l = S _ |- _ =>
      destruct l; cbn [length] in *; [ congruence | apply eq_add_S in H ]
    | H : length ?l = 0 |- _ =>
      destruct l; cbn [length] in *; [ | congruence ]
    end.

Section DestructListsByLengthTests.
  (* list with length 0 *)
  Goal (forall (l : list nat),
           length l = 0 -> l = nil).
  Proof.
    intros. destruct_lists_by_length.
    (* since l should be destructed, [nil=nil] should be left over *)
    exact (eq_refl nil).
  Qed.

  (* list with length (S n) *)
  Goal (forall (l : list nat) (n : nat),
           length l = S n -> length (tl l) = n).
  Proof.
    intros. destruct_lists_by_length.
    (* we should now have an expression of the form tl (_ :: _) *)
    progress cbn [tl]. assumption.
  Qed.

  (* multiple constant-length lists *)
  Goal (forall (l1 l2 : list nat),
           length l1 = 1 ->
           length l2 = 2 ->
           length (l1 ++ l2) = 3).
  Proof.
    intros. destruct_lists_by_length.
    (* now, we expect l1 and l2 to be fully destructed *)
    match goal with
    | |- length ((_ :: nil) ++ (_ :: _ :: nil)) = 3 => idtac
    end.
    reflexivity.
  Qed.
End DestructListsByLengthTests.

(* tactic that helps insert existentials for hypotheses with [List.map] *)
Ltac map_inversion H :=
  lazymatch type of H with
  | map _ _ = _ :: _ =>
    let H' := fresh in
    apply map_eq_cons in H; destruct H as [? [? [? [? H']]]];
    map_inversion H'
  | map _ _ = _ ++ _ =>
    let H' := fresh in
    let H'' := fresh in
    apply map_eq_app in H; destruct H as [? [? [? [H' H'']]]];
    map_inversion H';
    map_inversion H''
  | map _ _ = [] => apply map_eq_nil in H
  | _ => idtac
  end.

Section MapInversionTests.
  (* simple application of map_eq_nil *)
  Goal (forall (f : nat -> nat) (l : list nat), map f l = nil -> l = nil).
  Proof.
    intros *. intro H.
    map_inversion H.
    assumption.
  Qed.

  (* cons/snoc, recursive pattern *)
  Goal (forall (f : nat -> nat) (l1 l2 : list nat) (x y : nat),
           map f l1 = x :: l2 ++ [y] ->
           exists a b l3, f a = x /\ f b = y /\ map f l3 = l2).
  Proof.
    intros *. intro Hmap.
    map_inversion Hmap. subst.
    repeat eexists; eauto.
  Qed.
End MapInversionTests.

(* Prove two lists are equal by proving each element is equal *)
Ltac fequal_list :=
  repeat match goal with
         | |- cons _ _ = cons _ _ => f_equal
         end.

(* infer information from hypotheses including [In] *)
Ltac invert_in :=
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
         end.

(* Factor out loops from a goal in preparation for using fold_left_invariant *)
Ltac factor_out_loops' loop_defn :=
  lazymatch goal with
  | |- ?G =>
    lazymatch G with
    | context [(loop_defn ?A1 ?B1 ?f1 ?ls1 ?b1)] =>
      let F1 :=
          lazymatch (eval pattern (loop_defn A1 B1 f1 ls1 b1) in G) with
          | ?F _ => F end in
      lazymatch F1 with
      | context [(loop_defn ?A2 ?B2 ?f2 ?ls2 ?b2)] =>
        (unify ls1 ls2 + fail "Failed to unify loop lists:" ls1 ls2);
        let F2 :=
            lazymatch (eval pattern (loop_defn A2 B2 f2 ls2 b2) in F1) with
            | ?F _ => F end in
        (change (F2 (loop_defn A2 B2 f2 ls2 b2) (loop_defn A1 B1 f1 ls1 b1))
         || let loop1 := constr:(loop_defn A1 B1 f1 ls1 b1) in
           let loop2 := constr:(loop_defn A2 B2 f2 ls2 b2) in
           fail "Failed to change goal with:" F2 loop2 loop1)
      end
    end
  end.
Ltac factor_out_loops :=
  lazymatch goal with
  | |- context [fold_left] => factor_out_loops' constr:(@fold_left)
  | |- context [fold_left_accumulate] => factor_out_loops' constr:(@fold_left_accumulate)
  end.
