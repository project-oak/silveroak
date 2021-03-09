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
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Import ListNotations VectorNotations.
Local Open Scope list_scope.

Require Import coqutil.Tactics.Tactics.
Require Import ExtLib.Structures.Monads.
Export MonadNotation.

Require Import Cava.Cava.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Util.Identity.
Require Import Cava.Semantics.CombinationalProperties.
Require Import Cava.Lib.UnsignedAdders.
Require Import Cava.Lib.MultiplexersProperties.

Require Import DoubleCountBy.DoubleCountBy.

Existing Instance CombinationalSemantics.

(* redefine simpl_ident to simplify the new semantics class *)
Definition bvadd {n} (a b : Vector.t bool n) : Vector.t bool n :=
  N2Bv_sized n (Bv2N b + Bv2N a).

Definition bvsum {n} (l : list (Vector.t bool n)) : Vector.t bool n :=
  fold_left bvadd l (N2Bv_sized n 0).

Definition boolsum {n} (l : list bool) : Vector.t bool n :=
  fold_left (fun acc (c : bool) => if c then N2Bv_sized n (Bv2N acc + 1) else acc)
            l (N2Bv_sized n 0).

Definition bvaddc {n} (a b : Vector.t bool n) : Vector.t bool n * bool :=
  let sum := (Bv2N b + Bv2N a)%N in
  let carry := (Bv2N a <? sum mod (2 ^ N.of_nat n))%N in
  (N2Bv_sized n sum, carry).

Definition bvsumc {n} (l : list (Vector.t bool n)) : Vector.t bool n * bool :=
  fold_left (fun acc_c => bvaddc (fst acc_c)) l (N2Bv_sized n 0, false).

Definition count_by_spec (i : list (Vector.t bool 8)) : list (Vector.t bool 8 * bool) :=
  map (fun t => bvsumc (firstn t i)) (seq 1 (length i)).

Definition double_count_by_spec (i : list (Vector.t bool 8)) : list (Vector.t bool 8) :=
  map (fun t => boolsum (firstn t (map snd (count_by_spec i)))) (seq 1 (length i)).

Lemma addN_correct {n} (x y : combType (Vec Bit n)) :
  addN (x, y) = bvadd x y.
Admitted.
Hint Rewrite @addN_correct : simpl_ident.

Lemma ltV_correct {n m} x y :
  ltV (n:=n) (m:=m) (x, y) = (Bv2N x <? Bv2N y)%N.
Admitted.
Hint Rewrite @ltV_correct : simpl_ident.

Lemma addC_correct {n} (x y : combType (Vec Bit n)) :
  addC (x, y) = bvaddc x y.
Proof.
  cbv [addC bvaddc]. cbv [CombinationalSemantics].
  simpl_ident. cbv [bvadd].
  rewrite Bv2N_N2Bv_sized_modulo.
  rewrite N.add_comm. reflexivity.
Qed.
Hint Rewrite @addC_correct : simpl_ident.

Lemma incrN_correct {n} (x : combType (Vec Bit (S n))) :
  incrN x = N2Bv_sized (S n) (Bv2N x + 1).
Proof.
  cbv [incrN].
  cbn [CombinationalSemantics unpackV packV unsignedAdd unsignedAddBool constant].
  simpl_ident. cbn [Nat.max Nat.add Bv2N N.succ_double].
  (* just proof about shiftout from here *)
Admitted.
Hint Rewrite @incrN_correct : simpl_ident.

Lemma bvaddc_comm {n} (a b : Vector.t bool n) : bvaddc a b = bvaddc b a.
Admitted.
Local Opaque bvaddc.

Lemma count_by_step (input st : combType (Vec Bit 8)) :
  step count_by (tt, (tt, st)) input
  = (snd (bvaddc input st), (tt, (tt, fst (bvaddc input st)))).
Proof.
  intros; cbv [count_by Loop step].
  repeat first [ destruct_pair_let | progress simpl_ident].
  reflexivity.
Qed.

Lemma bvsumc_snoc {n} xs (x : t bool n) :
  bvsumc (xs ++ [x]) = bvaddc x (fst (bvsumc xs)).
Proof.
  cbv [bvsumc].
  autorewrite with pull_snoc.
  apply bvaddc_comm.
Qed.

Lemma boolsum_snoc {n} xs (x : bool) :
  boolsum (xs ++ [x]) = if x then N2Bv_sized n (Bv2N (n:=n) (boolsum xs) + 1) else boolsum xs.
Proof.
  cbv [boolsum]. autorewrite with pull_snoc.
  reflexivity.
Qed.

Lemma count_by_correct (input : list (combType (Vec Bit 8))) :
  simulate count_by input = map snd (count_by_spec input).
Proof.
  intros; cbv [count_by].
  eapply (simulate_Loop_invariant (s:=Vec Bit 8)) with
      (I:=fun t st _ acc =>
            st = fst (bvsumc (firstn t input))
            /\ acc = map snd (count_by_spec (firstn t input))).
  { (* invariant holds at start *)
    split; reflexivity. }
  { (* invariant holds through body *)
    cbv zeta. intros ? ? ? ? d; intros; logical_simplify; subst.
    cbv [step count_by_spec].
    repeat first [ destruct_pair_let | progress simpl_ident].
    rewrite firstn_succ_snoc with (d0:=d) by length_hammer.
    autorewrite with push_length natsimpl pull_snoc.
    rewrite Nat.add_1_r. autorewrite with pull_snoc.
    rewrite firstn_succ_snoc with (d0:=d) by length_hammer.
    cbv [combType] in *. rewrite !bvsumc_snoc.
    autorewrite with push_nth push_firstn push_length natsimpl listsimpl.
    ssplit; [ reflexivity | ].
    f_equal; [ ]. apply f_equal.
    apply map_ext_in; intros.
    match goal with H : _ |- _ => apply in_seq in H end.
    autorewrite with push_length natsimpl push_firstn push_list_fold listsimpl.
    reflexivity. }
  { (* invariant implies postcondition *)
    intros; logical_simplify; subst.
    rewrite firstn_all; reflexivity. }
Qed.

Lemma count_by_spec_nth t input d :
  t < length input ->
  nth t (count_by_spec input) d = bvaddc (nth t input (fst d)) (fst (bvsumc (firstn t input))).
Proof.
  cbv [count_by_spec]. intros.
  rewrite map_nth_inbounds with (d2:=0) by length_hammer.
  autorewrite with push_nth. cbn [Nat.add].
  rewrite firstn_succ_snoc with (d0:=fst d) by length_hammer.
  rewrite bvsumc_snoc. reflexivity.
Qed.

Lemma count_by_spec_length input : length (count_by_spec input) = length input.
Proof. cbv [count_by_spec]; length_hammer. Qed.
Hint Rewrite @count_by_spec_length using solve [eauto] : push_length.

Lemma firstn_count_by_spec t input :
  firstn t (count_by_spec input) = count_by_spec (firstn t input).
Proof.
  cbv [count_by_spec]. intros.
  autorewrite with push_firstn push_length natsimpl.
  apply map_ext_in; intros.
  match goal with H : _ |- _ => apply in_seq in H end.
  autorewrite with push_firstn natsimpl.
  reflexivity.
Qed.
Hint Rewrite @firstn_count_by_spec using solve [eauto] : push_firstn.

Lemma double_count_by_correct (input : list (combType (Vec Bit 8))) :
  simulate double_count_by input = double_count_by_spec input.
Proof.
  intros; cbv [double_count_by].
  let f := lazymatch goal with |- context [Loop ?body] => body end in
  eapply simulate_Loop_invariant
    with (body:=f)
         (I:= fun t st body_st acc =>
                body_st = (tt, (tt, fst (bvsumc (firstn t input))), tt)
                /\ st = boolsum (firstn t (map snd (count_by_spec input)))
                /\ acc = double_count_by_spec (firstn t input)).
  { (* invariant holds at start *)
    ssplit; reflexivity. }
  { (* invariant holds through body *)
    cbv zeta. intros ? ? ? ? d; intros; logical_simplify; subst.
    cbn [step]. cbv [double_count_by_spec].
    repeat first [ destruct_pair_let | progress simpl_ident].
    autorewrite with push_length natsimpl pull_snoc.
    rewrite !count_by_step. cbn [fst snd].
    cbv [combType] in *.
    rewrite firstn_succ_snoc with (d0:=d) by length_hammer.
    rewrite !firstn_succ_snoc with (d0:=false) by length_hammer.
    cbv [combType] in *. rewrite !bvsumc_snoc, !boolsum_snoc.
    rewrite !map_nth_inbounds with (d2:=(d,false)) by length_hammer.
    rewrite !count_by_spec_nth by length_hammer.
    ssplit; [ reflexivity .. | ].
    autorewrite with push_nth push_firstn push_length natsimpl listsimpl.
    f_equal; [ ].
    apply map_ext_in; intros.
    match goal with H : _ |- _ => apply in_seq in H end.
    autorewrite with push_firstn push_length natsimpl listsimpl.
    reflexivity. }
  { (* invariant implies postcondition *)
    intros; logical_simplify; subst.
    rewrite firstn_all; reflexivity. }
Qed.
