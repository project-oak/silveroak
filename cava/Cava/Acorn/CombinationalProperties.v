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
Require Import Cava.Acorn.Combinational.
Require Import Cava.Acorn.Identity.
Require Import Cava.BitArithmetic.
Require Import Cava.ListUtils.
Require Import Cava.NatUtils.
Require Import Cava.Signal.
Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
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

Lemma zipWith_correct {A B C : SignalType} n
      (f : combType A * combType B -> cava (combType C))
      (va : combType (Vec A n)) (vb : combType (Vec B n)) :
  unIdent (@zipWith _ _ A B C n f va vb)
  = Vector.map2 (fun a b => unIdent (f (a,b))) va vb.
Proof.
  cbv [zipWith]; intros. simpl_ident.
  rewrite map_vcombine_map2. reflexivity.
Qed.
Hint Rewrite @zipWith_correct using solve [eauto] : simpl_ident.

Lemma xorV_correct n a b :
  unIdent (@xorV _ _ n (a,b)) = Vector.map2 xorb a b.
Proof.
  intros. cbv [xorV]. cbn [fst snd].
  simpl_ident. apply map2_ext; intros.
  reflexivity.
Qed.
Hint Rewrite @xorV_correct using solve [eauto] : simpl_ident.


Lemma all_correct {n} v :
  unIdent (all (n:=n) v) = Vector.fold_left andb true v.
Proof.
  destruct n; [ eapply case0 with (v:=v); reflexivity | ].
  cbv [all]. cbn [one CombinationalSemantics].
  erewrite tree_all_sizes_equiv with (op:=andb) (id:=true);
    intros; simpl_ident; boolsimpl; try reflexivity; try lia;
      auto using Bool.andb_assoc.
Qed.
Hint Rewrite @all_correct using solve [eauto] : simpl_ident.

Lemma eqb_correct {t} (x y : combType t) :
  unIdent (eqb x y) = combType_eqb x y.
Proof.
  revert x y.
  induction t;
    cbn [eqb and2 xnor2 one unpair
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
  { (* Pair case *)
    simpl_ident. cbn [split]. repeat destruct_pair_let.
    cbn [fst snd]. rewrite IHt1, IHt2.
    cbn [combType_eqb].
    reflexivity. }
Qed.

Lemma eqb_eq {t} (x y : combType t) :
  unIdent (eqb x y) = true <-> x = y.
Proof.
  rewrite eqb_correct. split.
  { inversion 1. apply combType_eqb_true_iff. auto. }
  { intros; subst. f_equal.
    apply combType_eqb_true_iff. reflexivity. }
Qed.

Lemma eqb_refl {t} (x : combType t) : unIdent (eqb x x) = true.
Proof. apply eqb_eq. reflexivity. Qed.

Lemma eqb_neq {t} (x y : combType t) : x <> y ->  unIdent (eqb x y) = false.
Proof.
  rewrite eqb_correct; intros. f_equal.
  apply Bool.not_true_is_false.
  rewrite combType_eqb_true_iff. auto.
Qed.

Lemma eqb_nat_to_bitvec_sized sz n m :
  n < 2 ^ sz -> m < 2 ^ sz ->
  unIdent (eqb (t:=Vec Bit sz) (nat_to_bitvec_sized sz n)
               (nat_to_bitvec_sized sz m))
  = if Nat.eqb n m then true else false.
Proof.
  intros; destruct_one_match; subst; [ solve [apply (eqb_refl (t:=Vec Bit sz))] | ].
  apply (eqb_neq (t:=Vec Bit sz)). cbv [nat_to_bitvec_sized].
  rewrite N2Bv_sized_eq_iff with (n:=sz) by auto using N.size_nat_le_nat.
  lia.
Qed.

Lemma muxPair_correct {t} (i0 i1 : combType t) (sel : combType Bit) :
  unIdent (muxPair sel (i0, i1)) = if sel then i1 else i0.
Proof. destruct sel; reflexivity. Qed.
Hint Rewrite @muxPair_correct using solve [eauto] : simpl_ident.

Lemma indexAt2_correct {t} (i0 i1 : combType t) (sel : combType Bit) :
  indexAt [i0; i1]%vector [sel]%vector = if sel then i1 else i0.
Proof. destruct sel; reflexivity. Qed.
Hint Rewrite @indexAt2_correct using solve [eauto] : simpl_ident.

Lemma mux4_correct {t} (i0 i1 i2 i3 : combType t) (sel : combType (Vec Bit 2)) :
  mux4Tuple (i0,i1,i2,i3) sel =
  if Vector.hd (Vector.tl sel)
  then if Vector.hd sel then i3 else i2
  else if Vector.hd sel then i1 else i0.
Proof.
  cbv in sel. constant_bitvec_cases sel; reflexivity.
Qed.
Hint Rewrite @mux4_correct using solve [eauto] : simpl_ident.

Lemma indexConst_eq {A sz} (v : combType (Vec A sz)) (n : nat) :
  indexConst v n = nth_default (defaultCombValue _) n v.
Proof. reflexivity. Qed.
Hint Rewrite @indexConst_eq using solve [eauto] : simpl_ident.

Lemma fork2Correct {A} (i : combType A) :
 unIdent (fork2 i) = (i, i).
Proof. reflexivity. Qed.
Hint Rewrite @fork2Correct using solve [eauto] : simpl_ident.
