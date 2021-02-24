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

Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Import ListNotations VectorNotations.
Local Open Scope list_scope.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.

Require Import Cava.Cava.
Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.Circuit.
Require Import Cava.Acorn.Identity.
Require Import Cava.Acorn.Combinational.
Require Import Cava.Acorn.Combinators.
Require Import Cava.Acorn.Multistep.
Require Import Cava.Lib.UnsignedAdders.

Require Import DoubleCountBy.DoubleCountBy.

Existing Instance CombinationalSemantics.

(* redefine simpl_ident to simplify the new semantics class *)
Ltac simpl_ident ::=
  repeat (first
            [ progress autorewrite with simpl_ident
            | progress cbn[fst snd bind ret Monad_ident monad
                               CombinationalSemantics unIdent] ]).

Definition bvadd {n} (a b : Vector.t bool n) : Vector.t bool n :=
  N2Bv_sized n (Bv2N b + Bv2N a).

Definition bvsum {n} (l : list (Vector.t bool n)) : Vector.t bool n :=
  fold_left bvadd l (N2Bv_sized n 0).

Definition bvaddc {n} (a b : Vector.t bool n) : Vector.t bool n * bool :=
  let sum := (Bv2N b + Bv2N a)%N in
  let carry := (Bv2N a <? sum mod (2 ^ N.of_nat n))%N in
  (N2Bv_sized n sum, carry).

Definition bvsumc {n} (l : list (Vector.t bool n)) : Vector.t bool n * bool :=
  fold_left (fun '(acc,_) => bvaddc acc) l (N2Bv_sized n 0, false).

Definition count_by_spec (i : list (Vector.t bool 8)) : list (Vector.t bool 8 * bool) :=
  map (fun t => bvsumc (firstn t i)) (seq 1 (length i)).

Definition double_count_by_spec (i : list (Vector.t bool 8)) : list (Vector.t bool 8 * bool) :=
  map (fun t => bvsumc (firstn t i)) (seq 1 (length i)).

Lemma addN_correct {n} (x y : combType (Vec Bit n)) :
  unIdent (addN (x, y)) = bvadd x y.
Admitted.
Hint Rewrite @addN_correct : simpl_ident.

Lemma ltV_correct {n m} x y :
  unIdent (ltV (n:=n) (m:=m) (x, y)) = (Bv2N x <? Bv2N y)%N.
Admitted.
Hint Rewrite @ltV_correct : simpl_ident.

Lemma addC_correct {n} (x y : combType (Vec Bit n)) :
  unIdent (addC (x, y)) = bvaddc x y.
Proof.
  cbv [addC bvaddc]. cbv [CombinationalSemantics].
  simpl_ident. cbv [bvadd].
  rewrite Bv2N_N2Bv_sized_modulo.
  rewrite N.add_comm. reflexivity.
Qed.
Hint Rewrite @addC_correct : simpl_ident.

Lemma incrN_correct {n} (x : combType (Vec Bit (S n))) :
  unIdent (incrN x) = N2Bv_sized (S n) (Bv2N x + 1).
Proof.
  cbv [incrN].
  cbn [CombinationalSemantics peel unpeel unsignedAdd unsignedAddBool constant].
  simpl_ident. cbn [Nat.max Nat.add Bv2N N.succ_double].
  (* just proof about shiftout from here *)
Admitted.
Hint Rewrite @incrN_correct : simpl_ident.

Lemma bvaddc_comm {n} (a b : Vector.t bool n) : bvaddc a b = bvaddc b a.
Admitted.
Local Opaque bvaddc.

Lemma count_by_correct (input : list (combType (Vec Bit 8))) :
  multistep count_by input
  = map snd (count_by_spec input).
Proof.
  destruct input as [|input0 input]; [ reflexivity | ].
  cbv [multistep count_by_spec count_by Loop step].
  rewrite <-seq_shift, map_map. cbn [firstn].
  repeat destruct_pair_let. simpl_ident.
  repeat destruct_pair_let. simpl_ident.
  erewrite fold_left_accumulate_ext_In.
  2:{ intros; repeat destruct_pair_let; simpl_ident.
      instantiate_app_by_reflexivity. }
  rewrite fold_left_accumulate_to_seq with (default:=defaultCombValue _).
  cbv [fold_left_accumulate fold_left_accumulate']. cbn [app].

  pose (statet := combType (Vec Bit 8)).
  pose (outt := combType Bit).
  pose (to_out_and_state:=fun (x : statet * outt) => (snd x, (tt, (tt, fst x)))).
  (* Important: min_state should go *inside fold_left to avoid this complicated state type *)
  eapply fold_left_invariant_seq
      with (I:=fun i (acc_st : list (outt * (unit * (unit * statet))) * (outt * (unit * (unit * statet)))) =>
                 acc_st = (map to_out_and_state (count_by_spec (firstn (S i) (input0 :: input))),
                           to_out_and_state (bvsumc (firstn (S i) (input0 :: input))))).
  { (* invariant holds at start *)
    subst_lets. cbn - [bvaddc].
    rewrite bvaddc_comm. reflexivity. }
  { (* invariant holds through loop *)
    intros. Tactics.destruct_products. subst_lets.
    logical_simplify. cbn [fst snd].
    cbv [bvsumc]. cbn [fold_left].
    autorewrite with push_firstn push_length.
    rewrite !Min.min_l by (cbn [combType] in *; Lia.lia).
    cbn [seq map].
    rewrite <-!seq_shift, !map_map. cbn [fold_left].
    erewrite !firstn_succ_snoc with (d:=defaultCombValue _) by length_hammer.
    autorewrite with pull_snoc. repeat destruct_pair_let.
    f_equal; [ | rewrite bvaddc_comm; reflexivity ].

    cbv [count_by_spec bvsumc].
    autorewrite with push_length natsimpl.
    rewrite PeanoNat.Nat.add_1_r.
    rewrite <-seq_shift, !map_map.
    rewrite seq_snoc. cbn [seq].
    rewrite <-!app_comm_cons. cbn [map].
    autorewrite with pull_snoc push_firstn.
    cbn [fold_left].
    apply f_equal.
    apply f_equal2.
    { rewrite <-seq_shift, !map_map.
      apply map_ext_in; intros *.
      rewrite in_seq. intros.
      cbn [combType] in *.
      autorewrite with push_firstn push_length natsimpl listsimpl.
      reflexivity. }
    { cbn [combType] in *.
      autorewrite with push_length push_firstn natsimpl.
      autorewrite with pull_snoc. repeat destruct_pair_let.
      cbn [fst snd]. rewrite bvaddc_comm. reflexivity. }
  }
  { (* invariant implies postcondition *)
    intros. Tactics.destruct_products. logical_simplify.
    subst_lets. cbn [fst snd map seq].
    cbv [bvsumc]. cbn [fold_left].
    autorewrite with push_length natsimpl.
    cbn [map seq firstn fold_left fst snd].
    f_equal. rewrite <-!seq_shift, !map_map.
    apply map_ext; intros. cbn [fst snd].
    autorewrite with push_firstn. cbn [fold_left].
    reflexivity. }
Qed.
