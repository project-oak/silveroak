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
Require Import Cava.Core.CavaClass.
Require Import Cava.Acorn.CavaPrelude.
Require Import Cava.Acorn.Combinators.
Require Import Cava.Acorn.Combinational.
Require Import Cava.Acorn.Identity.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.List.
Require Import Cava.Util.Nat.
Require Import Cava.Core.Signal.
Require Import Cava.Util.Tactics.
Require Import Cava.Util.Vector.
Require Import Cava.Lib.BitVectorOps.
Import VectorNotations ListNotations.
Local Open Scope list_scope.

Existing Instance CombinationalSemantics.

(* Equality of combinational signals is decidable *)
Section DecidableEquality.
  Fixpoint combType_eqb {t} : combType t -> combType t -> bool :=
    match t as t0 return combType t0 -> combType t0 -> bool with
    | Void => fun _ _ => true
    | Bit => fun x y => Bool.eqb x y
    | Vec A n => fun x y => Vector.eqb _ combType_eqb x y
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
             end.
  Qed.
End DecidableEquality.

Lemma zipWith_correct {A B C : SignalType} n
      (f : combType A * combType B -> cava (combType C))
      (va : combType (Vec A n)) (vb : combType (Vec B n)) :
  @zipWith _ _ A B C n f va vb
  = Vector.map2 (fun a b => f (a,b)) va vb.
Proof.
  cbv [zipWith]; intros. simpl_ident.
  rewrite map_vcombine_map2. reflexivity.
Qed.
Hint Rewrite @zipWith_correct using solve [eauto] : simpl_ident.

Lemma xorV_correct n a b :
  @xorV _ _ n (a,b) = Vector.map2 xorb a b.
Proof.
  intros. cbv [xorV]. cbn [fst snd].
  simpl_ident. apply map2_ext; intros.
  reflexivity.
Qed.
Hint Rewrite @xorV_correct using solve [eauto] : simpl_ident.

Lemma pow2tree_equiv
      {t} (id : combType t) (op : combType t -> combType t -> combType t)
      (op_id_left : forall a : combType t, op id a = a)
      (op_id_right : forall a : combType t, op a id = a)
      (op_assoc :
         forall a b c : combType t,
           op a (op b c) = op (op a b) c)
      (circuit : combType t * combType t -> cava (combType t))
      (circuit_equiv : forall a b, circuit (a, b) = op a b)
      (n : nat) :
  forall v,
    pow2tree n circuit v = Vector.fold_left op id v.
Proof.
  cbv [pow2tree]; intros. simpl_ident.
  erewrite pow2tree_generic_equiv with (circuit0 := (fun a b => circuit (a, b)));
    eauto; intros; reflexivity.
Qed.

Lemma tree_equiv {t} :
  forall (id : combType t) (op : combType t -> combType t -> combType t),
    (forall a : combType t, op id a = a) ->
    (forall a : combType t, op a id = a) ->
    (forall a b c : combType t, op a (op b c) = op (op a b) c) ->
    forall circuit : combType t * combType t -> cava (combType t),
      (forall a b : combType t, circuit (a, b) = op a b) ->
      forall (n : nat) (v : combType (Vec t n)),
        n <> 0 ->
        tree circuit v = Vector.fold_left op id v.
Proof.
  intros. cbv [tree]. simpl_ident.
  eapply (tree_generic_equiv (semantics:=CombinationalSemantics)); eauto.
Qed.

Lemma all_correct {n} v :
  all (n:=n) v = Vector.fold_left andb true v.
Proof.
  destruct n; [ eapply case0 with (v:=v); reflexivity | ].
  cbv [all]. simpl_ident.
  eapply (tree_equiv (t:=Bit));
    intros; boolsimpl; try reflexivity; try lia;
      auto using Bool.andb_assoc.
Qed.
Hint Rewrite @all_correct using solve [eauto] : simpl_ident.

Lemma eqb_correct {t} (x y : combType t) :
  eqb x y = combType_eqb x y.
Proof.
  revert x y.
  induction t;
    cbn [eqb and2 xnor2 one
             CombinationalSemantics] in *;
    intros; simpl_ident; repeat destruct_pair_let;
    (* handle easy cases first *)
    repeat lazymatch goal with
           | x : unit |- _ => destruct x
           | x : combType Bit |- _ => destruct x
           | |- (?x = ?x <-> ?y = ?y) => split; reflexivity
           | _ => first [ progress cbn [List.map combine fst snd xnorb xorb negb]
                       | split; (congruence || reflexivity) ]
           end.
  { (* Vector case *)
    simpl_ident. cbn [combType_eqb].
    rewrite eqb_fold. apply f_equal.
    auto using map2_ext. }
Qed.

Lemma eqb_eq {t} (x y : combType t) :
  eqb x y = true <-> x = y.
Proof.
  rewrite eqb_correct. split.
  { inversion 1. apply combType_eqb_true_iff. auto. }
  { intros; subst. f_equal.
    apply combType_eqb_true_iff. reflexivity. }
Qed.

Lemma eqb_refl {t} (x : combType t) : eqb x x = true.
Proof. apply eqb_eq. reflexivity. Qed.

Lemma eqb_neq {t} (x y : combType t) : x <> y ->  eqb x y = false.
Proof.
  rewrite eqb_correct; intros. f_equal.
  apply Bool.not_true_is_false.
  rewrite combType_eqb_true_iff. auto.
Qed.

Lemma eqb_nat_to_bitvec_sized sz n m :
  n < 2 ^ sz -> m < 2 ^ sz ->
  eqb (t:=Vec Bit sz) (nat_to_bitvec_sized sz n)
      (nat_to_bitvec_sized sz m)
  = if Nat.eqb n m then true else false.
Proof.
  intros; destruct_one_match; subst; [ solve [apply (eqb_refl (t:=Vec Bit sz))] | ].
  apply (eqb_neq (t:=Vec Bit sz)). cbv [nat_to_bitvec_sized].
  rewrite N2Bv_sized_eq_iff with (n:=sz) by auto using N.size_nat_le_nat.
  lia.
Qed.

Lemma indexAt2_correct {t} (i0 i1 : combType t) (sel : combType Bit) :
  indexAt [i0; i1]%vector [sel]%vector = if sel then i1 else i0.
Proof. destruct sel; reflexivity. Qed.
Hint Rewrite @indexAt2_correct using solve [eauto] : simpl_ident.

Lemma indexConst_eq {A sz} (v : combType (Vec A sz)) (n : nat) :
  indexConst v n = nth_default (defaultCombValue _) n v.
Proof. reflexivity. Qed.
Hint Rewrite @indexConst_eq using solve [eauto] : simpl_ident.

Lemma fork2Correct {A} (i : combType A) :
 fork2 i = (i, i).
Proof. reflexivity. Qed.
Hint Rewrite @fork2Correct using solve [eauto] : simpl_ident.
