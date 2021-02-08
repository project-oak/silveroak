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
Require Import Coq.NArith.NArith.
Require Import Coq.Vectors.Vector.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.CavaPrelude.
Require Import Cava.Acorn.Combinators.
Require Import Cava.Acorn.CombinationalMonad.
Require Import Cava.Acorn.Identity.
Require Import Cava.BitArithmetic.
Require Import Cava.ListUtils.
Require Import Cava.NatUtils.
Require Import Cava.Signal.
Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
Import VectorNotations ListNotations.
Local Open Scope list_scope.

Existing Instance CircuitSemantics.

Section LastSignal.
  Lemma lastSignal_nil {A} : @lastSignal A [] = defaultCombValue A.
  Proof. reflexivity. Qed.
  Lemma lastSignal_cons {A} a0 a :
    a <> [] -> @lastSignal A (a0 :: a) = lastSignal a.
  Proof. destruct a; [ congruence | reflexivity ]. Qed.
  Lemma lastSignal_map {A B} (f : combType A -> combType B) (a : seqType A) :
    f (defaultCombValue A) = defaultCombValue B ->
    lastSignal (List.map f a) = f (lastSignal a).
  Proof.
    cbv [lastSignal]. intros.
    induction a as [|a0 a]; [ cbn; congruence | ].
    destruct a; [ reflexivity | ].
    cbn [List.map List.last] in *. auto.
  Qed.
  Lemma lastSignal_map_seq {A} (f : nat -> combType A) start len :
    len <> 0 ->
    lastSignal (List.map f (seq start len)) = f (start + (len - 1)).
  Proof.
    destruct len; intros; [ congruence | ].
    autorewrite with pull_snoc natsimpl.
    cbv [lastSignal]. rewrite last_last. reflexivity.
  Qed.
  Lemma lastSignal_nth {A} (l : seqType A) n d :
    l <> [] -> n = length l - 1 ->
    List.nth n l d = lastSignal l.
  Proof.
    intros; cbv [lastSignal].
    rewrite nth_last by auto. subst.
    induction l; [ congruence | ].
    cbn [List.last]. destruct l; [ reflexivity | ].
    apply IHl; congruence.
  Qed.
End LastSignal.

Section PadCombine.
  Lemma pad_combine_eq {A B} a b :
    length a = length b -> @pad_combine A B a b = combine a b.
  Proof.
    cbv [pad_combine]; intros.
    rewrite !extend_le by lia.
    reflexivity.
  Qed.

  Lemma pad_combine_nil_r {A B} a :
    @pad_combine A B a [] = List.map (fun a => (a, defaultCombValue B)) a.
  Proof.
    cbv [pad_combine]. autorewrite with push_extend.
    rewrite combine_repeat_r by length_hammer. reflexivity.
  Qed.

  Lemma pad_combine_nil_l {A B} b :
    @pad_combine A B [] b = List.map (fun b => (defaultCombValue A, b)) b.
  Proof.
    cbv [pad_combine]. autorewrite with push_extend.
    rewrite combine_repeat_l by length_hammer. reflexivity.
  Qed.

  Lemma pad_combine_cons {A B} a b la lb :
    la <> [] -> lb <> [] ->
    @pad_combine A B (a :: la) (b :: lb) = (a,b) :: pad_combine la lb.
  Proof.
    cbv [pad_combine]. autorewrite with push_length push_extend.
    cbn [combine]. intros. f_equal; [ ].
    destruct la, lb; intros; [ congruence .. | ].
    autorewrite with push_length push_extend.
    rewrite lastSignal_cons by congruence. reflexivity.
  Qed.

  Lemma pad_combine_length {A B} a b :
    @length (combType (Pair A B))
            (@pad_combine A B a b) = Nat.max (length a) (length b).
  Proof. cbv [pad_combine]. cbn [combType]. length_hammer. Qed.

  Lemma pad_combine_to_nth {A B} (a : seqType A) (b : seqType B) :
    pad_combine a b = List.map (fun n => (List.nth n a (lastSignal a),
                                       List.nth n b (lastSignal b)))
                               (seq 0 (Nat.max (length a) (length b))).
  Proof.
    revert b; induction a as [|a0 a]; intros.
    { rewrite pad_combine_nil_l. cbn [length List.nth Nat.max].
      rewrite map_to_nth with (d:=lastSignal b).
      apply List.map_ext; intros.
      destruct_one_match; reflexivity. }
    { destruct b.
      { rewrite pad_combine_nil_r.
        cbn [length seq Nat.max List.map].
        rewrite <-seq_shift, List.map_map.
        autorewrite with push_nth. f_equal; [ ].
        erewrite map_to_nth.
        apply List.map_ext; intros. reflexivity. }
      { destruct a, b; [ reflexivity | cbv [pad_combine] .. | ];
        repeat match goal with
               | _ => progress cbn [combine repeat Nat.max seq List.map]
               | _ => erewrite combine_repeat_l by reflexivity
               | _ => erewrite combine_repeat_r by reflexivity
               | _ => rewrite <-seq_shift, List.map_map by auto
               | _ => rewrite pad_combine_cons by congruence
               | _ => rewrite IHa by auto
               | |- ?x :: _ = ?x :: _ => f_equal; [ ]
               | |- List.map ?f ?x = List.map ?g (seq 0 (length ?x)) =>
                 erewrite map_to_nth with (ls:=x)
               | |- List.map ?f ?x = List.map ?g ?x => apply List.map_ext; intros
               | _ => progress
                       autorewrite with push_length push_extend push_nth
               | _ => reflexivity
               end. } }
  Qed.

  Lemma nth_pad_combine_inbounds {A B} (a : seqType A) (b : seqType B) n d :
    n < Nat.max (length a) (length b) ->
    List.nth n (pad_combine a b) d = (List.nth n a (lastSignal a),
                                      List.nth n b (lastSignal b)).
  Proof.
    intros.
    rewrite nth_inbounds_change_default with (d2:=(lastSignal a, lastSignal b))
      by (rewrite (@pad_combine_length A B); lia).
    cbv [pad_combine]. rewrite combine_nth by apply extend_to_match.
    rewrite !nth_extend; reflexivity.
  Qed.
End PadCombine.
Hint Rewrite @pad_combine_length using solve [eauto] : push_length.

Section Pairs.
  Lemma unpair_skipn {A B} n (l : seqType (Pair A B)) :
    unpair (skipn n l) = (skipn n (fst (unpair l)), skipn n (snd (unpair l))).
  Proof. apply split_skipn. Qed.
  Lemma unpair_mkpair {A B} (a : seqType A) (b : seqType B) :
    length a = length b ->
    unpair (mkpair a b) = (a, b).
  Proof.
    cbv [mkpair unpair CircuitSemantics]; intros.
    rewrite pad_combine_eq by lia.
    apply combine_split; lia.
  Qed.
  Lemma unpair_mkpair_pad_combine {A B} (a : seqType A) (b : seqType B) :
    unpair (mkpair a b) =
    (List.map (A:=combType (Pair A B))
              (@fst (combType A) (combType B)) (pad_combine a b),
     List.map (A:=combType (Pair A B))
              (@snd (combType A) (combType B)) (pad_combine a b)).
  Proof.
    cbv [mkpair unpair CircuitSemantics]; intros.
    rewrite split_map. reflexivity.
  Qed.
End Pairs.

Section Peel.
  Lemma fold_left_map2_peel A B n (f : combType B -> combType A -> combType B)
        (v : combType (Vec A n)) (start : combType B) :
    fold_left (map2 f) [start] (peel [v]) = [fold_left f start v].
  Proof.
    cbn [peel CircuitSemantics].
    revert v start; induction n; [ intros; eapply case0 with (v:=v); reflexivity | ].
    intros v start; rewrite (eta v). fold combType. cbn [combType].
    rewrite peelVecList_cons_cons.
    autorewrite with push_vector_fold push_vector_map vsimpl.
    cbn [map2]. rewrite IHn. reflexivity.
  Qed.

  Lemma peel_length_InV {A} n (vs : seqType (Vec A n)) l :
    InV l (peel vs) -> length l = length vs.
  Proof. apply peelVecList_length. Qed.

  Lemma peel_length_ForallV {A} n (vs : seqType (Vec A n)) :
    ForallV (fun l => length l = length vs) (peel vs).
  Proof.
    cbv [peel peelVecList indexConstBoolList CircuitSemantics].
    apply ForallV_forall. intros *.
    rewrite InV_map_iff; intros [? [? ?]]. subst.
    length_hammer.
  Qed.

  Lemma map_nth_default_vseq' {A} d n m (v : Vector.t A (n + m)) :
    Vector.map (fun i => nth_default d i v) (vseq 0 n) = fst (splitat _ v).
  Proof.
    apply to_list_inj. autorewrite with push_to_list.
    revert v; induction n; intros; [ reflexivity | ].
    autorewrite with pull_snoc natsimpl.
    rewrite firstn_succ_snoc with (d0:=d) by length_hammer.
    change (S n + m) with (S (n + m)) in *.
    rewrite (eta_snoc v).
    autorewrite with push_to_list push_firstn push_length natsimpl listsimpl vsimpl.
    rewrite <-IHn; f_equal; [ | ].
    { apply List.map_ext_in. intros *; rewrite in_seq; intros.
      apply nth_default_snoc; lia. }
    { rewrite nth_default_to_list.
      autorewrite with push_to_list. reflexivity. }
  Qed.

  Lemma map_nth_default_vseq {A} d n (v : Vector.t A n) :
    Vector.map (fun i => nth_default d i v) (vseq 0 n) = v.
  Proof.
    replace v with (resize_default d n (resize_default d (n + 0) v))
      by (rewrite resize_default_resize_default, resize_default_id by lia;
          reflexivity).
    erewrite map_ext by (intros;rewrite nth_default_resize_default by lia;
                         instantiate_app_by_reflexivity).
    rewrite map_nth_default_vseq'.
    rewrite resize_default_resize_default, resize_default_id by lia.
    apply to_list_inj. autorewrite with push_to_list.
    rewrite firstn_all2 by length_hammer. reflexivity.
  Qed.

  Lemma map_nth_default_seq' {A} d n (l : list A) :
    n <= length l -> List.map (fun i => List.nth i l d) (seq 0 n) = firstn n l.
  Proof.
    revert l; induction n; [ destruct l; reflexivity | ].
    intros. autorewrite with pull_snoc natsimpl.
    rewrite firstn_succ_snoc with (d0:=d) by lia.
    rewrite IHn by lia; reflexivity.
  Qed.

  Lemma map_nth_default_seq {A} d n (l : list A) :
    length l = n -> List.map (fun i => List.nth i l d) (seq 0 n) = l.
  Proof.
    intros; rewrite map_nth_default_seq' by lia.
    rewrite firstn_all2 by lia; reflexivity.
  Qed.

  Lemma unpeel_peel A n (v : seqType (Vec A n)) :
    n <> 0 -> unpeel (peel v) = v.
  Proof.
    cbv [unpeel peel unpeelVecList peelVecList CircuitSemantics].
    cbv [indexConstBoolList]. intros.
    erewrite max_length_same_length with (len:=length v); [ | | lia .. ];
      [ | intros *; rewrite InV_map_iff; intros [? [? ?]]; subst;
          solve [length_hammer] ].
    erewrite List.map_ext_in.
    2:{ intros *. rewrite in_seq; intros.
        rewrite map_map.
        erewrite Vector.map_ext_in.
        2:{
          intros.
          rewrite map_nth_inbounds with (d2:=Vector.const (defaultCombValue _) _)
            by (cbn [combType] in *; lia).
          instantiate_app_by_reflexivity. }
        rewrite map_nth_default_vseq.
        instantiate_app_by_reflexivity. }
    rewrite map_nth_default_seq; reflexivity.
  Qed.
End Peel.

Section DecidableEquality.
  Fixpoint combType_eqb {t} : combType t -> combType t -> bool :=
    match t as t0 return combType t0 -> combType t0 -> bool with
    | Void => fun _ _ => true
    | Bit => fun x y => Bool.eqb x y
    | Vec A n => fun x y => Vector.eqb _ combType_eqb x y
    | Pair A B => fun x y =>
                   (combType_eqb (fst x) (fst y) &&
                    combType_eqb (snd x) (snd y))%bool
    | ExternalType s => fun x y => true
    end.

  Lemma combType_eqb_true_iff {t} (x y : combType t) :
    combType_eqb x y = true <-> x = y.
  Proof.
    revert x y; induction t; intros;
      repeat match goal with
             | _ => progress cbn [combType_eqb combType Bool.eqb fst snd] in *
             | x : unit |- _ => destruct x
             | x : bool |- _ => destruct x
             | x : _ * _ |- _ => destruct x
             | _ => tauto
             | _ => solve [eauto using VectorEq.eqb_eq]
             | |- _ <-> _ => split; congruence
             end; [ ].
    (* only the pair case should be remaining *)
    rewrite Bool.andb_true_iff, IHt1, IHt2.
    split; [ destruct 1 | inversion 1; split ];
      intros; subst; eauto.
  Qed.
End DecidableEquality.

Lemma all_correct {n} v :
  unIdent (all (n:=n) [v]) = [Vector.fold_left andb true v].
Proof.
  destruct n; [ eapply Vector.case0 with (v:=v); reflexivity | ].
  cbv [all]. cbn [one CircuitSemantics].
  erewrite tree_all_sizes_equiv' with (op:=map2 andb) (id:=[true]) (valid:=fun a => length a = 1);
    intros; destruct_lists_by_length;
      cbn [map2 length unIdent Monad.bind Monad.ret Monad_ident]; boolsimpl;
        try reflexivity; try lia.
  { apply fold_left_map2_peel with (A:=Bit) (B:=Bit). }
  { f_equal; apply Bool.andb_assoc. }
  { apply ForallV_forall; intros.
    lazymatch goal with H : InV _ _ |- _ =>
                        eapply (peel_length_InV (A:=Bit)) in H end.
    length_hammer. }
Qed.

Lemma eqb_correct {t} (x y : combType t) :
  unIdent (eqb [x] [y]) = [combType_eqb x y].
Proof.
  revert x y.
  induction t;
    cbn [eqb combType and2 xnor2 one unpair
             CircuitSemantics] in *; cbv [lift2];
    intros; simpl_ident; repeat destruct_pair_let;
    (* handle easy cases first *)
    repeat lazymatch goal with
           | x : unit |- _ => destruct x
           | x : bool |- _ => destruct x
           | |- (?x = ?x <-> ?y = ?y) => split; reflexivity
           | _ => first [ progress cbn [List.map combine fst snd xnorb xorb negb]
                       | rewrite pad_combine_eq by length_hammer
                       | split; (congruence || reflexivity) ]
           end.
  { (* Vector case *)
    destruct (Nat.eq_dec n 0); subst;
      [ repeat match goal with
               | x : Vector.t _ 0 |- _ => eapply case0 with (v:=x); clear x
               end; split; reflexivity | ].
    erewrite (zipWith_unIdent (A:=t) (B:=t) (C:=Bit)) by eauto.
    rewrite (all_correct (n:=n)). cbn [combType_eqb].
    rewrite eqb_fold. reflexivity. }
  { (* Pair case *)
    simpl_ident. cbn [split]. repeat destruct_pair_let.
    cbn [fst snd]. rewrite IHt1, IHt2.
    rewrite pad_combine_eq by length_hammer.
    cbn [combine List.map fst snd combType_eqb].
    reflexivity. }
Qed.

Lemma eqb_eq {t} (x y : combType t) :
  unIdent (eqb [x] [y]) = [true] <-> x = y.
Proof.
  rewrite eqb_correct. split.
  { inversion 1. apply combType_eqb_true_iff. auto. }
  { intros; subst. f_equal.
    apply combType_eqb_true_iff. reflexivity. }
Qed.

Lemma eqb_refl {t} (x : combType t) : unIdent (eqb [x] [x]) = [true].
Proof. apply eqb_eq. reflexivity. Qed.

Lemma eqb_neq {t} (x y : combType t) : x <> y ->  unIdent (eqb [x] [y]) = [false].
Proof.
  rewrite eqb_correct; intros. f_equal.
  apply Bool.not_true_is_false.
  rewrite combType_eqb_true_iff. auto.
Qed.

Lemma eqb_nat_to_bitvec_sized sz n m :
  n < 2 ^ sz -> m < 2 ^ sz ->
  unIdent (eqb (t:=Vec Bit sz) [nat_to_bitvec_sized sz n]
               [nat_to_bitvec_sized sz m])
  = [if Nat.eqb n m then true else false].
Proof.
  intros; destruct_one_match; subst; [ solve [apply (eqb_refl (t:=Vec Bit sz))] | ].
  apply (eqb_neq (t:=Vec Bit sz)). cbv [nat_to_bitvec_sized].
  rewrite N2Bv_sized_eq_iff with (n:=sz) by auto using N.size_nat_le_nat.
  lia.
Qed.

Lemma pairSel_mkpair_singleton {t} (x y : combType t) (sel : bool) :
  pairSel [sel] (mkpair [x] [y]) = [if sel then y else x].
Proof. destruct sel; reflexivity. Qed.

Lemma max_length_uniform_length {A} n (v : Vector.t (list A) n) len :
  n <> 0 -> ForallV (fun l => length l = len) v ->
  fold_left Nat.max 0 (map (@length A) v) = len.
Proof.
  destruct n; [ congruence | ]. intro H; clear H.
  cbn [ForallV]; intros [? ?].
  assert (0 <= len) by lia. generalize dependent 0.
  generalize dependent v.
  induction n; cbn [ForallV]; intros;
    autorewrite with push_vector_fold push_vector_map vsimpl;
    cbn [Nat.max]; repeat match goal with H : _ /\ _ |- _ => destruct H end;
      [ lia | ].
  erewrite <-IHn with (v:=tl v);
    [ autorewrite with push_vector_fold push_vector_map vsimpl;
      reflexivity | .. ].
  all:auto; lia.
Qed.

Lemma indexAt_unpeel' {A} n isz
      (v : Vector.t (seqType A) n) (sel : Vector.t (seqType Bit) isz) vlen sellen :
  n <> 0 -> isz <> 0 -> sellen <> 0 -> vlen <> 0 ->
  ForallV (fun s => length s = vlen) v ->
  ForallV (fun s => length s = sellen) sel ->
  indexAt (unpeel v) (unpeel sel) =
  List.map
    (fun t =>
       let sel := map (fun s => List.nth t s (lastSignal s)) sel in
       let v := map (fun s => List.nth t s (lastSignal s)) v in
       nth_default (defaultCombValue A) (N.to_nat (Bv2N sel)) v)
    (seq 0 (Nat.max vlen sellen)).
Proof.
  intros ? ? ? ? Hv Hsel; cbn [indexAt unpeel CircuitSemantics].
  cbv [indexAtBoolList unpeelVecList].
  erewrite map_to_nth with (ls:=@pad_combine (Vec Bit isz) (Vec A n) _ _)
                           (d:=(defaultCombValue (Vec Bit isz), defaultCombValue (Vec A n))).
  autorewrite with push_length.
  erewrite !max_length_uniform_length, Nat.max_comm by eauto.
  apply List.map_ext_in. intro i; rewrite in_seq; intros.
  rewrite nth_pad_combine_inbounds by length_hammer.
  rewrite ForallV_forall in Hv.
  rewrite ForallV_forall in Hsel.
  f_equal; [ destr (i <? sellen) | destr (i <? vlen) ];
    repeat lazymatch goal with
           | |- N.to_nat _ = N.to_nat _ => f_equal
           | |- Bv2N _ = Bv2N _ => f_equal
           | |- Vector.map _ ?v = Vector.map _ ?v => apply map_ext_InV; intros
           | H : InV _ sel |- _ => apply Hsel in H
           | H : InV _ v |- _ => apply Hv in H
           | |- List.nth ?n ?l ?d1 = List.nth ?n ?l ?d2 =>
             apply nth_inbounds_change_default;
               cbn [combType] in *; fold combType; solve [length_hammer]
           | |- @lastSignal ?A (List.map _ (seq _ _)) = _ =>
             rewrite (@lastSignal_map_seq A) by auto
           | _ => first [ progress autorewrite with push_nth natsimpl
                       | rewrite lastSignal_nth
                         by (try apply length_pos_nonnil; length_hammer)
                       | reflexivity ]
           end.
Qed.

Lemma unpeel_uniform_length {A} n (v : Vector.t (seqType A) n) len :
  n <> 0 -> ForallV (fun s => length s = len) v ->
  length (unpeel v) = len.
Proof.
  destruct n; [ congruence | ].
  intros ? Hv. cbn [unpeel CircuitSemantics].
  cbv [unpeelVecList]. erewrite max_length_uniform_length by eauto.
  length_hammer.
Qed.

Lemma indexAt_unpeel {A} n isz
      (v : Vector.t (seqType A) n) (sel : Vector.t (seqType Bit) isz) vlen sellen :
  n <> 0 -> isz <> 0 ->
  ForallV (fun s => length s = vlen) v ->
  ForallV (fun s => length s = sellen) sel ->
  indexAt (unpeel v) (unpeel sel) =
  List.map
    (fun t =>
       let sel := map (fun s => List.nth t s (lastSignal s)) sel in
       let v := map (fun s => List.nth t s (lastSignal s)) v in
       nth_default (defaultCombValue A) (N.to_nat (Bv2N sel)) v)
    (seq 0 (Nat.max vlen sellen)).
Proof.
  intros ? ? Hv Hsel.
  (* use indexAt_unpeel' to solve the case where both are nonzero *)
  destr (sellen =? 0); [ | destr (vlen =? 0) ]; subst;
    [ pose proof (unpeel_uniform_length isz sel 0 ltac:(auto) ltac:(auto))
    | pose proof (unpeel_uniform_length n v 0 ltac:(auto) ltac:(auto))
    | apply indexAt_unpeel'; solve [auto] ].
  (* separately prove cases where one or the other input is 0-length *)
  all:repeat lazymatch goal with
             | H : length ?v = 0 |- _ =>
               destruct v; [ clear H | cbn [length] in *; congruence ]
             | |- context [indexAt] =>
               progress cbn [indexAt unpeel CircuitSemantics];
                 cbv [indexAtBoolList unpeelVecList]
             | |- List.map _ ?l = List.map _ ?l =>
               apply List.map_ext_in; intros *; rewrite in_seq; intros;
                 rewrite ForallV_forall in Hsel; rewrite ForallV_forall in Hv
             | |- nth_default ?d _ _ = nth_default ?d _ _ => f_equal
             | |- N.to_nat _ = N.to_nat _ => f_equal
             | |- Bv2N _ = Bv2N _ => f_equal
             | |- defaultCombValue ?A = map _ _ =>
               rewrite map_ext_InV with (g:=fun _ => defaultCombValue _);
                 [ rewrite map_to_const; reflexivity | intros ]
             | |- map _ ?v = map _ ?v => apply map_ext_InV; intros
             | |- List.nth ?n ?l ?d1 = List.nth ?n ?l ?d2 =>
               apply nth_inbounds_change_default
             | Hv: (forall x, InV x ?v -> _), Hin : InV ?l ?v |- _ =>
               apply Hv in Hin
             | |- ?x = ?x => reflexivity
             | _ => first [ rewrite pad_combine_nil_l
                         | rewrite pad_combine_nil_r
                         | erewrite max_length_uniform_length by eauto
                         | rewrite List.map_map
                         | rewrite Nat.max_0_r
                         | rewrite Nat.max_0_l
                         | rewrite lastSignal_nil
                         | progress autorewrite with push_nth
                         | solve [length_hammer] ]
             end.
Qed.

Lemma pairSel_mkpair {t} (x y : seqType t) (sel : seqType Bit) :
  pairSel sel (mkpair x y) = List.map
                               (fun (xysel : combType t * combType t * combType Bit) =>
                                  let '(x,y,sel) := xysel in
                                  if sel then y else x)
                               (pad_combine (pad_combine x y) sel).
Proof.
  cbv [pairSel]. intros. rewrite unpair_mkpair_pad_combine.
  rewrite !indexAt_unpeel with
      (sellen :=length sel) (vlen := Nat.max (length x) (length y))
      by (try congruence; cbn [ForallV]; ssplit; try reflexivity;
          autorewrite with vsimpl; length_hammer).
  autorewrite with vsimpl push_length.
  cbn [Vector.map].
  rewrite !(pad_combine_to_nth _ sel), List.map_map.
  autorewrite with push_length.
  eapply List.map_ext_in.
  intro i; rewrite in_seq. intros.
  repeat destruct_pair_let.
  cbn [Bv2N N.succ_double N.double].
  destr (i <? Nat.max (length x) (length y));
    [ erewrite !map_nth_inbounds with (d2:=lastSignal (pad_combine x y))
      by length_hammer; destruct_one_match; reflexivity | ].
  rewrite !nth_overflow with (l:=List.map _ _) by length_hammer.
  rewrite !nth_overflow with (l:=pad_combine _ _) by length_hammer.
  rewrite !lastSignal_map by reflexivity.
  destruct_one_match; reflexivity.
Qed.

Lemma pairAssoc_mkpair {A B C} a b c :
  @pairAssoc _ _ A B C (mkpair (mkpair [a] [b]) [c]) = mkpair [a] (mkpair [b] [c]).
Proof. reflexivity. Qed.
Lemma unpair_default {A B} :
  unpair [defaultCombValue (Pair A B)] = ([defaultCombValue A], [defaultCombValue B]).
Proof. reflexivity. Qed.

Lemma unpair_nth {A B} (p : seqType (Pair A B)) n d :
  List.nth n p d = (List.nth n (fst (unpair p)) (fst d),
                    List.nth n (snd (unpair p)) (snd d)).
Proof. apply split_nth. Qed.

Lemma muxPair_correct {t} (i0 i1 : combType t) (sel : combType Bit) :
  unIdent (muxPair [sel] (([i0] : seqType _), ([i1] : seqType _))) = [if sel then i1 else i0].
Proof. destruct sel; reflexivity. Qed.

Lemma mkpair_single {A B} (a : combType A) (b : seqType B):
  length b <> 0 ->
  mkpair [a] b = mkpair (repeat a (length b)) b.
Proof.
  intros; cbv [mkpair pad_combine CircuitSemantics].
  cbv [lastSignal]. cbn [List.last].
  destruct b; cbn [length] in *; [ lia | ].
  cbn [repeat]; rewrite repeat_cons, last_last.
  cbv [extend]. autorewrite with push_length natsimpl.
  cbn [repeat]. autorewrite with listsimpl.
  rewrite <-repeat_cons. reflexivity.
Qed.

Lemma mkpair_one {t} (x : seqType t):
  length x <> 0 ->
  mkpair one x = mkpair (repeat true (length x)) x.
Proof.
  intros; cbn [one constant CircuitSemantics].
  rewrite (mkpair_single (A:=Bit)) by auto.
  reflexivity.
Qed.

Lemma mkpair_zero {t} (x : seqType t):
  length x <> 0 ->
  mkpair zero x = mkpair (repeat false (length x)) x.
Proof.
  intros; cbn [zero constant CircuitSemantics].
  rewrite (mkpair_single (A:=Bit)) by auto.
  reflexivity.
Qed.

Lemma fst_unpair {A B} (ab : seqType (Pair A B)) :
  fst (unpair ab) = List.map fst ab.
Proof.
  cbv [unpair CircuitSemantics].
  induction ab; [ reflexivity | ].
  cbn [split List.map].
  repeat destruct_pair_let.
  rewrite <-IHab. reflexivity.
Qed.

Lemma snd_unpair {A B} (ab : seqType (Pair A B)) :
  snd (unpair ab) = List.map snd ab.
Proof.
  cbv [unpair CircuitSemantics].
  induction ab; [ reflexivity | ].
  cbn [split List.map].
  repeat destruct_pair_let.
  rewrite <-IHab. reflexivity.
Qed.

Lemma mux4_mkpair {t} (i0 i1 i2 i3 : combType t) (sel : combType (Vec Bit 2)) :
  mux4 (mkpair (mkpair (mkpair [i0] [i1]) [i2]) [i3]) [sel] =
  [if Vector.hd (Vector.tl sel)
   then if Vector.hd sel then i3 else i2
   else if Vector.hd sel then i1 else i0].
Proof.
  cbv in sel. constant_vector_simpl sel.
  cbv [mux4 indexConst CircuitSemantics].
  autorewrite with vsimpl.
  repeat
    match goal with
    | |- context [(@indexConstBoolList ?t ?sz ?v ?n)] =>
      let x := constr:(@indexConstBoolList t sz v n) in
      let y := (eval cbn in x) in
      progress change x with y
    | _ => rewrite pairAssoc_mkpair
    | _ => rewrite pairSel_mkpair
    | _ => destruct_one_match
    | _ => reflexivity
    end.
Qed.
