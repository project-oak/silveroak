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
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import Coq.Vectors.Vector.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.Combinators.
Require Import Cava.Acorn.CombinationalMonad.
Require Import Cava.Acorn.Identity.
Require Import Cava.BitArithmetic.
Require Import Cava.NatUtils.
Require Import Cava.Signal.
Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
Import VectorNotations.

Existing Instance CombinationalSemantics.

Lemma all_fold_left {n} v :
  unIdent (all (n:=n) v) = Vector.fold_left andb true v.
Proof.
  destruct n; [ eapply Vector.case0 with (v:=v); reflexivity | ].
  cbv [all]. cbn [one CombinationalSemantics].
  rewrite MonadLaws.bind_of_return by apply MonadLaws_ident.
  erewrite tree_all_sizes_equiv with (op:=andb) (id:=true);
    auto using Bool.andb_true_r, Bool.andb_true_l, Bool.andb_assoc.
Qed.

Lemma eqb_eq {t} (x y : combType t) :
  unIdent (eqb x y) = true <-> x = y.
Proof.
  revert x y.
  induction t;
    cbn [eqb combType and2 andBool xnor2 xnorBool one
             CombinationalSemantics] in *;
    intros; simpl_ident; repeat destruct_pair_let;
    (* handle easy cases first *)
    repeat lazymatch goal with
           | x : unit |- _ => destruct x
           | x : bool |- _ => destruct x; cbn [xorb negb]
           | |- (?x = ?x <-> ?y = ?y) => split; reflexivity
           end;
    try (split; congruence); [ ].
  { (* Vector case *)
    rewrite (zipWith_unIdent (C:=Bit)).
    rewrite <-fold_andb_eq_iff by apply IHt.
    rewrite all_fold_left. reflexivity. }
Qed.

Lemma eqb_refl {t} (x : combType t) : unIdent (eqb x x) = true.
Proof. apply eqb_eq. reflexivity. Qed.

Lemma eqb_neq {t} (x y : combType t) : x <> y ->  unIdent (eqb x y) = false.
Proof. rewrite <-Bool.not_true_iff_false, eqb_eq. tauto. Qed.

Lemma eqb_nat_to_bitvec_sized sz n m :
  n < 2 ^ sz -> m < 2 ^ sz ->
  unIdent (eqb (t:=Vec Bit sz) (nat_to_bitvec_sized sz n)
               (nat_to_bitvec_sized sz m))
  = if Nat.eqb n m then true else false.
Proof.
  intros; destruct_one_match; subst; [ solve [apply eqb_refl] | ].
  apply eqb_neq. cbv [nat_to_bitvec_sized].
  rewrite N2Bv_sized_eq_iff with (n:=sz) by auto using N.size_nat_le_nat.
  lia.
Qed.

Lemma mux2_unIdent' {t} (i0 i1 : combType t) sel :
  @unIdent (combType t) (mux2 (A:=ione t) sel (i0, i1)) = if sel then i1 else i0.
Proof.
  cbv [mux2 on_bits2].
  revert sel i0 i1; induction t; intros;
    cbn [on_bits2' fst snd signals signals_gen combType] in *;
    repeat match goal with
           | x : unit |- _ => destruct x
           | _ => destruct_one_match; reflexivity
           end; [ ].
  { (* Vector case *)
    simpl_ident.
    erewrite map2_ext by (intros; rewrite IHt; instantiate_app_by_reflexivity).
    destruct_one_match; [ rewrite map2_swap | ];
      rewrite map2_drop; apply map_id_ext; reflexivity. }
Qed.

Lemma mux2_unIdent {t} (i0 i1 : signals t) sel :
  unIdent (mux2 sel (i0, i1)) = if sel then i1 else i0.
Proof.
  cbv [mux2].
  revert sel i0 i1; induction t; intros; [ solve [apply mux2_unIdent'] | ].
  cbn [on_bits2]. simpl_ident. rewrite IHt1, IHt2.
  destruct i0,i1. cbn [fst snd].
  destruct_one_match; reflexivity.
Qed.
Hint Rewrite @mux2_unIdent using solve [eauto] : simpl_ident.

Lemma mux4_unIdent {t} (i0 i1 i2 i3 : combType t) sel :
  unIdent (mux4 (i0, i1, i2, i3) sel) =
  if Vector.hd (Vector.tl sel)
  then if Vector.hd sel then i3 else i2
  else if Vector.hd sel then i1 else i0.
Proof.
  cbv in sel. constant_vector_simpl sel. autorewrite with vsimpl.
  cbv [mux4 pairRight Monad.mcompose]; cbn [indexConst CombinationalSemantics].
  simpl_ident.
  repeat
    match goal with
    | |- context [(@indexConstBool ?t ?sz ?v ?n)] =>
      let x := constr:(@indexConstBool t sz v n) in
      let y := (eval cbn in x) in
      progress change x with y
    | _ => progress cbn [signals signals_gen]
    | _ => rewrite mux2_unIdent'
    | _ => destruct_one_match
    | _ => reflexivity
    end.
Qed.

Lemma one_correct : @unIdent (combType Bit) one = true.
Proof. reflexivity. Qed.
Hint Rewrite one_correct using solve [eauto] : simpl_ident.

Lemma zero_correct : @unIdent (combType Bit) zero = false.
Proof. reflexivity. Qed.
Hint Rewrite zero_correct using solve [eauto] : simpl_ident.
