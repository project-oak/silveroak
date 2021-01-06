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
    cbn [eqb combType and2 andBool xnor2 xnorBool one unpair
             CombinationalSemantics] in *;
    intros; simpl_ident; repeat destruct_pair_let;
    (* handle easy cases first *)
    repeat lazymatch goal with
           | x : unit |- _ => destruct x
           | x : bool |- _ => destruct x; cbn [xorb negb]
           | |- (?x = ?x <-> ?y = ?y) => split; reflexivity
           end;
    try (split; congruence); [ | ].
  { (* Vector case *)
    match goal with
    | |- context [(@unIdent (Vector.t bool ?n) (zipWith _ _ _))] =>
      change (Vector.t bool n) with (combType (Vec Bit n));
        rewrite zipWith_unIdent
    end.
    rewrite <-fold_andb_eq_iff by apply IHt.
    rewrite all_fold_left. reflexivity. }
  { (* Pair case *)
    simpl_ident. rewrite pair_equal_spec, <-IHt1, <-IHt2.
    rewrite Bool.andb_true_iff. reflexivity. }
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

Lemma pairSel_mkpair {t} (x y : combType t) (sel : bool) :
  pairSel sel (mkpair x y) = if sel then y else x.
Proof. reflexivity. Qed.

Lemma pairAssoc_mkpair {A B C} a b c :
  @pairAssoc _ _ A B C (mkpair (mkpair a b) c) = mkpair a (mkpair b c).
Proof. reflexivity. Qed.

Lemma mux4_mkpair {t} (i0 i1 i2 i3 : combType t) sel :
  mux4 (mkpair (mkpair (mkpair i0 i1) i2) i3) sel =
  if Vector.hd (Vector.tl sel)
  then if Vector.hd sel then i3 else i2
  else if Vector.hd sel then i1 else i0.
Proof.
  cbv in sel. constant_vector_simpl sel.
  cbv [mux4 indexConst CombinationalSemantics].
  autorewrite with vsimpl.
  repeat
    match goal with
    | |- context [(@indexConstBool ?t ?sz ?v ?n)] =>
      let x := constr:(@indexConstBool t sz v n) in
      let y := (eval cbn in x) in
      progress change x with y
    | _ => rewrite pairAssoc_mkpair
    | _ => rewrite pairSel_mkpair
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

Lemma half_adder_correct (input : combType Bit * combType Bit) :
  combinational (half_adder input)
  = (xorb (fst input) (snd input), andb (fst input) (snd input)).
Proof.
  cbv [half_adder combinational and2 xor2 CombinationalSemantics
                  xorBool andBool].
  repeat destruct_pair_let. simpl_ident.
  reflexivity.
Qed.
Hint Rewrite half_adder_correct using solve [eauto] : simpl_ident.

Lemma incr4_correct (input : combType (Vec Bit 4)) :
  combinational (incr4 input) = N2Bv_sized 4 (Bv2N input + 1).
Proof.
  cbv [incr4 combinational]. simpl_ident. boolsimpl.
  cbn [unpeel indexConst CombinationalSemantics].
  cbn [combType] in input. constant_bitvec_cases input.
  all:reflexivity.
Qed.

Lemma half_subtractor_correct (input : combType Bit * combType Bit) :
  combinational (half_subtractor input)
  = (xorb (fst input) (snd input), andb (negb (fst input)) (snd input)).
Proof.
  cbv [half_subtractor combinational and2 xor2 inv
                       CombinationalSemantics xorBool andBool].
  repeat destruct_pair_let. simpl_ident.
  reflexivity.
Qed.
Hint Rewrite half_subtractor_correct using solve [eauto] : simpl_ident.

Lemma decr4_correct (input : combType (Vec Bit 4)) :
  combinational (decr4 input) = N2Bv_sized 4 (if (Bv2N input =? 0)%N then 15
                                              else Bv2N input - 1).
Proof.
  cbv [decr4 combinational]. simpl_ident. boolsimpl.
  cbn [unpeel indexConst CombinationalSemantics].
  cbn [combType] in input. constant_bitvec_cases input.
  all:reflexivity.
Qed.

Lemma incr'_correct {sz} carry (input : combType (Vec Bit sz)) :
  combinational (incr' carry input)
  = N2Bv_sized _ (Bv2N input + if carry then 1 else 0)%N.
Proof.
  cbv [combinational].
  revert carry input; induction sz; intros; [ solve [apply nil_eq] | ].
  cbn [incr']. simpl_ident. cbn [unpeel peel CombinationalSemantics].
  rewrite (eta input). autorewrite with vsimpl.
  rewrite IHsz; clear IHsz.
  destruct carry, (Vector.hd input);
    boolsimpl; rewrite ?N.add_0_r, ?N2Bv_sized_Bv2N;
      try reflexivity; [ | ].
  (* TODO(jadep) : improve this proof *)
  { apply Bv2N_inj; autorewrite with push_Bv2N.
    compute_expr (N.of_nat 1). rewrite !Bv2N_N2Bv_sized_modulo.
    rewrite !N.double_spec, !N.succ_double_spec.
    rewrite Nat2N.inj_succ. rewrite N.pow_succ_r by lia.
    rewrite N.mod_mul_r by (try apply N.pow_nonzero; lia).
    lazymatch goal with
    | |- context [(2 * ?n + 1 + 1)%N] =>
      replace (2 * n + 1 + 1)%N with ((n + 1) * 2)%N by lia
    end.
    rewrite N.div_mul, N.mod_mul by lia.
    lia. }
  { autorewrite with push_Bv2N.
    rewrite N.double_succ_double.
    autorewrite with push_N2Bv_sized.
    rewrite N2Bv_sized_Bv2N.
    reflexivity. }
Qed.

Lemma incr_correct {sz} (input : combType (Vec Bit sz)) :
  combinational (incr input) = N2Bv_sized _ (Bv2N input + 1).
Proof. cbv [incr]. simpl_ident. apply incr'_correct. Qed.
