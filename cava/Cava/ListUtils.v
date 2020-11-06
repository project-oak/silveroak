Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Local Open Scope list_scope.

(* Generic rewrite database for common list simplifications *)
Hint Rewrite @app_nil_l @app_nil_r @last_last @rev_app_distr : listsimpl.

Section Length.
  Lemma nil_length {A} : @length A nil = 0.
  Proof. reflexivity. Qed.
  Lemma cons_length {A} x (ls : list A) : length (x :: ls) = S (length ls).
  Proof. reflexivity. Qed.
End Length.

(* The push_length autorewrite database simplifies goals including [length] *)
Hint Rewrite @nil_length @cons_length @seq_length @repeat_length @rev_length
     @map_length @firstn_length @skipn_length @app_length @combine_length
     using solve [eauto] : push_length.
Ltac length_hammer :=
  autorewrite with push_length; eauto; lia.

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
End Folds.
Hint Rewrite @fold_left_cons @fold_left_nil
     using solve [eauto] : push_list_fold.

(* Defines a version of fold_left that accumulates a list of (a
   projection of) all the states it passed through *)
Section FoldLeftAccumulate.
  Definition fold_left_accumulate' {A B C}
             (f : B -> A -> B) (g : B -> C) acc0 ls b : list C * B :=
    fold_left (fun '(acc, b) a => (acc ++ [g (f b a)], f b a))
              ls (acc0 ++ [g b], b).
  Definition fold_left_accumulate {A B C} (f : B -> A -> B) (g : B -> C) :=
    fold_left_accumulate' f g nil.

  Lemma fold_left_accumulate'_nil {A B C}
        (f : B -> A -> B) (g : B -> C) b acc0 :
    fst (fold_left_accumulate' f g acc0 [] b) = (acc0 ++ [g b]).
  Proof. reflexivity. Qed.

  Hint Rewrite @fold_left_accumulate'_nil : push_fold_acc.

  Lemma fold_left_accumulate'_cons {A B C}
        (f : B -> A -> B) (g : B -> C) b a acc0 ls :
    fst (fold_left_accumulate' f g acc0 (a::ls) b)
    = fst (fold_left_accumulate' f g (acc0 ++ [g b]) ls (f b a)).
  Proof. reflexivity. Qed.

  Hint Rewrite @fold_left_accumulate'_cons : push_fold_acc.

  Lemma fold_left_accumulate'_equiv {A B C}
        (f : B -> A -> B) (g : B -> C) b acc0 ls :
    fst (fold_left_accumulate' f g acc0 ls b)
    = (acc0 ++ fst (fold_left_accumulate' f g [] ls b)).
  Proof.
    revert acc0 b.
    induction ls; intros; autorewrite with push_fold_acc listsimpl;
      [ reflexivity | ].
    rewrite IHls with (acc0:=(_++_)).
    rewrite IHls with (acc0:=(_::_)).
    rewrite app_assoc_reverse.
    reflexivity.
  Qed.

  Lemma fold_left_accumulate'_snoc {A B C}
        (f : B -> A -> B) (g : B -> C) b a acc0 ls :
    fst (fold_left_accumulate' f g acc0 (ls ++ [a]) b)
    = let r := fold_left_accumulate' f g acc0 ls b in
      (fst r ++ [g (f (snd r) a)]).
  Proof.
    cbv zeta. revert acc0 b.
    induction ls; intros; rewrite <-?app_comm_cons;
      autorewrite with push_fold_acc listsimpl;
      [ reflexivity | ].
    rewrite IHls. reflexivity.
  Qed.

  Lemma fold_left_accumulate'_last {A B C}
        (f : B -> A -> B) (g : B -> C) b c acc0 ls :
    last (fst (fold_left_accumulate' f g acc0 ls b)) c = g (fold_left f ls b).
  Proof.
    revert acc0 b; induction ls; intros; cbn [fold_left];
      autorewrite with push_fold_acc; eauto using last_last.
  Qed.

  Lemma fold_left_accumulate'_length {A B C} (f : B -> A -> B) (g : B -> C) :
    forall ls acc0 b,
      length (fst (fold_left_accumulate'
                     f g acc0 ls b)) = length acc0 + S (length ls).
  Proof.
    induction ls; intros; autorewrite with push_fold_acc;
      rewrite ?IHls; length_hammer.
  Qed.

  Lemma fold_left_accumulate_nil {A B C} (f : B -> A -> B) (g : B -> C) b :
    fst (fold_left_accumulate f g [] b) = [g b].
  Proof. reflexivity. Qed.

  Lemma fold_left_accumulate_cons {A B C} (f : B -> A -> B) (g : B -> C) b a ls :
    fst (fold_left_accumulate f g (a::ls) b)
    = (g b :: fst (fold_left_accumulate f g ls (f b a))).
  Proof.
    cbv [fold_left_accumulate].
    autorewrite with push_fold_acc listsimpl.
    rewrite fold_left_accumulate'_equiv.
    reflexivity.
  Qed.

  Lemma fold_left_accumulate_snoc {A B C} (f : B -> A -> B) (g : B -> C) b a ls :
    fst (fold_left_accumulate f g (ls ++ [a]) b)
    = let r := fold_left_accumulate f g ls b in
      fst r ++ [g (f (snd r) a)].
  Proof.
    cbv [fold_left_accumulate].
    rewrite fold_left_accumulate'_snoc.
    reflexivity.
  Qed.

  Lemma fold_left_accumulate_last {A B C} (f : B -> A -> B) (g : B -> C) b c ls :
    last (fst (fold_left_accumulate f g ls b)) c = g (fold_left f ls b).
  Proof.
    cbv [fold_left_accumulate]. apply fold_left_accumulate'_last.
  Qed.

  Lemma fold_left_accumulate_length {A B C} (f : B -> A -> B) (g : B -> C) ls b :
    length (fst (fold_left_accumulate f g ls b)) = S (length ls).
  Proof.
    cbv [fold_left_accumulate].
    rewrite fold_left_accumulate'_length.
    reflexivity.
  Qed.

  Lemma map_fold_left_accumulate {A B C D}
        (f : B -> A -> B) (g : B -> C) (h : C -> D) ls b :
    map h (fst (fold_left_accumulate f g ls b)) =
    fst (fold_left_accumulate f (fun x => h (g x)) ls b).
  Proof.
    revert b.
    induction ls; intros; [ reflexivity | ].
    rewrite !fold_left_accumulate_cons, map_cons.
    rewrite IHls. reflexivity.
  Qed.

  Lemma fold_left_fold_left_accumulate {A B C D}
        (f : B -> A -> B) (g : B -> C) (h : D -> C -> D) :
    forall ls b d,
      fold_left
        h (fst (fold_left_accumulate f g ls b)) d =
      snd (fold_left
             (fun '(b,d) a => (f b a, h d (g (f b a))))
             ls (b, h d (g b))).
  Proof.
    induction ls; intros; [ reflexivity | ].
    rewrite fold_left_accumulate_cons.
    cbn [fold_left]. rewrite IHls.
    reflexivity.
  Qed.

  Lemma fold_left_accumulate'_snd {A B C}
        (f : B -> A -> B) (g : B -> C) :
    forall ls acc0 b,
      snd (fold_left_accumulate' f g acc0 ls b) = fold_left f ls b.
  Proof.
    cbv [fold_left_accumulate'].
    induction ls; intros; [ reflexivity | ].
    cbn [fold_left]. erewrite <-IHls.
    reflexivity.
  Qed.

  Lemma fold_left_accumulate_snd {A B C}
        (f : B -> A -> B) (g : B -> C) :
    forall ls b,
      snd (fold_left_accumulate f g ls b) = fold_left f ls b.
  Proof. intros; apply fold_left_accumulate'_snd. Qed.

  Lemma nth_fold_left_accumulate'_id {A B}
        (f : B -> A -> B) :
    forall ls acc0 b d i,
      length acc0 <= i <= length acc0 + length ls ->
      nth i (fst (fold_left_accumulate' f (fun x => x) acc0 ls b)) d =
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

  Lemma nth_fold_left_accumulate_id {A B}
        (f : B -> A -> B) :
    forall ls b d i,
      i <= length ls ->
      nth i (fst (fold_left_accumulate f (fun x => x) ls b)) d =
      fold_left f (firstn i ls) b.
  Proof.
    cbv [fold_left_accumulate]; intros.
    rewrite nth_fold_left_accumulate'_id by (cbn [length]; lia).
    rewrite Nat.sub_0_r. reflexivity.
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
