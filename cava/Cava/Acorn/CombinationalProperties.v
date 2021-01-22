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
Import ListNotations VectorNotations.
Local Open Scope list_scope.

Existing Instance CombinationalSemantics.

Section PadCombine.
  Lemma pad_combine_eq {A B} a b :
    length a = length b -> @pad_combine A B a b = combine a b.
  Proof.
    cbv [pad_combine]; intros.
    rewrite !extend_le by lia.
    reflexivity.
  Qed.
End PadCombine.

Section Pairs.
  Lemma unpair_skipn {A B} n (l : seqType (Pair A B)) :
    unpair (skipn n l) = (skipn n (fst (unpair l)), skipn n (snd (unpair l))).
  Proof. apply split_skipn. Qed.
  Lemma unpair_mkpair {A B} (a : seqType A) (b : seqType B) :
    length a = length b ->
    unpair (mkpair a b) = (a, b).
  Proof.
    cbv [mkpair unpair CombinationalSemantics]; intros.
    rewrite pad_combine_eq by lia.
    apply combine_split; lia.
  Qed.
End Pairs.

Section Peel.
  Lemma fold_left_map2_peel A B n (f : combType B -> combType A -> combType B)
        (v : combType (Vec A n)) (start : combType B) :
    fold_left (map2 f) [start] (peel [v]) = [fold_left f start v].
  Proof.
    cbn [peel CombinationalSemantics].
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
    cbv [peel peelVecList indexConstBoolList CombinationalSemantics].
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
    cbv [unpeel peel unpeelVecList peelVecList CombinationalSemantics].
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
  cbv [all]. cbn [one CombinationalSemantics].
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
             CombinationalSemantics] in *; cbv [lift2];
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

Lemma pairSel_mkpair {t} (x y : combType t) (sel : bool) :
  pairSel [sel] (mkpair [x] [y]) = [if sel then y else x].
Proof. cbn - [pairSel]. reflexivity. Qed.

Lemma pairAssoc_mkpair {A B C} a b c :
  @pairAssoc _ _ A B C (mkpair (mkpair [a] [b]) [c]) = mkpair [a] (mkpair [b] [c]).
Proof. reflexivity. Qed.

Lemma mux4_mkpair {t} (i0 i1 i2 i3 : combType t) (sel : combType (Vec Bit 2)) :
  mux4 (mkpair (mkpair (mkpair [i0] [i1]) [i2]) [i3]) [sel] =
  [if Vector.hd (Vector.tl sel)
   then if Vector.hd sel then i3 else i2
   else if Vector.hd sel then i1 else i0].
Proof.
  cbv in sel. constant_vector_simpl sel.
  cbv [mux4 indexConst CombinationalSemantics].
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
