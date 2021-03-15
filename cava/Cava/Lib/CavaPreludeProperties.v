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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Vectors.Vector.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Core.Core.
Require Import Cava.Lib.CavaPrelude.
Require Import Cava.Lib.CombinationalProperties.
Require Import Cava.Lib.CombinatorsProperties.
Require Import Cava.Lib.VecProperties.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.BitArithmeticProperties.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Tactics.
Require Import Cava.Util.Vector.

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
