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

Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import Coq.Vectors.Vector.
Require Import coqutil.Tactics.Tactics.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadLaws.
Require Import Cava.Core.Core.
Require Import Cava.Lib.Adders.
Require Import Cava.Lib.Combinators.
Require Import Cava.Lib.CombinationalProperties.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.BitArithmeticProperties.
Require Import Cava.Util.Identity.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Require Import Cava.Util.Vector.
Local Open Scope N_scope.

(* A proof that the half-adder is correct. *)
Lemma halfAdder_behaviour :
  forall (a : bool) (b : bool),
    halfAdder (a, b) = (xorb a b, a && b).
Proof.
  auto.
Qed.

(* A proof that the the full-adder is correct. *)
Lemma fullAdder_behaviour : forall (a : bool) (b : bool) (cin : bool),
    fullAdder (cin, (a, b))
    = (xorb cin (xorb a b),
       (a && b) || (b && cin) || (a && cin)).
Proof.
  intros.
  unfold fst.
  simpl.
  case a, b, cin.
  all : reflexivity.
Qed.

(* First prove the full-adder correct. *)

Lemma fullAdder_correct (cin a b : bool) :
  fullAdder (cin, (a, b)) =
  let sum := N.b2n a + N.b2n b + N.b2n cin in
  (N.testbit sum 0, N.testbit sum 1).
Proof. destruct cin, a, b; reflexivity. Qed.

(* Lemma about how to decompose a list of bits. *)
Lemma list_bits_to_nat_cons b bs :
  N.of_list_bits (b :: bs) = (N.b2n b + 2 * (N.of_list_bits bs))%N.
Proof.
  cbv [N.of_list_bits]. cbn [of_list length].
  rewrite Bv2N_cons.
  destruct_one_match; cbn [N.b2n];
    rewrite ?N.double_spec, ?N.succ_double_spec;
    lia.
Qed.

Hint Rewrite @bind_of_return @bind_associativity
     using solve [typeclasses eauto] : monadlaws.

(* Correctness of the list based adder. *)
Lemma addLCorrect (cin : bool) (a b : list bool) :
  length a = length b ->
  N.of_list_bits (addLWithCinL cin a b) =
  N.of_list_bits a + N.of_list_bits b + N.b2n cin.
Proof.
  cbv zeta. cbv [addLWithCinL adderWithGrowthL unsignedAdderL colL].
  cbn [fst snd].
  (* get rid of pair-let because it will cause problems in the inductive case *)
  simpl_ident. repeat destruct_pair_let.

  (* start induction; eliminate cases where length b <> length a and solve base
     case immediately *)
  revert dependent cin. revert dependent b.
  induction a; (destruct b; cbn [length]; try lia; [ ]); intros;
    [ destruct cin; reflexivity | ].

  (* inductive case only now; simplify *)
  cbn [combine colL']. rewrite !list_bits_to_nat_cons.
  simpl_ident.

  (* use fullAdder_correct to replace fullAdder call with addition + testbit *)
  rewrite fullAdder_correct. cbv zeta.
  (cbn match beta). repeat destruct_pair_let; simpl_ident.

  (* Rearrange to match inductive hypothesis *)
  rewrite <-app_comm_cons.
  rewrite list_bits_to_nat_cons.

  (* Finally we have the right expression to use IHa *)
  rewrite IHa by lia.

  (* Now that the recursive part matches, we can just compute all 8 cases for
     the first step (a + b + cin) *)
  destruct a, b, cin; cbv [N.b2n].
  all:repeat match goal with
             | |- context [N.testbit ?x ?n] =>
               let b := eval compute in (N.testbit x n) in
                   change (N.testbit x n) with b
             end; (cbn match).
  all:lia.
Qed.

(* Correctness of the vector based adder. *)

Lemma Bv2N_resize m n (Hmn : n = m) (v : t bool n) :
  Bv2N v = Bv2N (Vector.resize_default false m v).
Proof.
  subst. rewrite Vector.resize_default_id.
  reflexivity.
Qed.

Lemma colV_colL {A B C} {n} circuit inputs d :
  @colV _ CombinationalSemantics A B C n circuit inputs =
  (let inputL := (fst inputs, to_list (snd inputs)) in
   rL <- colL circuit inputL ;;
      let rV := Vector.resize_default
                  d _ (Vector.of_list (fst rL)) in
      ret (rV, snd rL)).
Proof.
  cbv [colV colL]. destruct inputs as [a bs]. cbn [fst snd].
  revert a; induction bs; intros.
  { cbn [colL' colV' to_list fst snd].
    autorewrite with monadlaws; reflexivity. }
  { rewrite !to_list_cons. cbn [colL' colV'].
    simpl_ident. repeat destruct_pair_let.
    simpl_ident. rewrite IHbs. clear IHbs.
    simpl_ident. cbn [fst snd of_list length].
    cbn [Vector.resize_default].
    autorewrite with vsimpl.
    reflexivity. }
Qed.

Lemma Bv2N_list_bits_to_nat n (v : t bool n) :
  Bv2N v = N.of_list_bits (to_list v).
Proof.
  induction v; intros; [ reflexivity | ].
  rewrite to_list_cons, Bv2N_cons, list_bits_to_nat_cons.
  destruct_one_match; cbn [N.b2n];
    rewrite ?N.double_spec, ?N.succ_double_spec;
    lia.
Qed.

Lemma colL_length {A B C} circuit a bs :
  length (fst (@colL ident _ A B C circuit (a,bs)))
  = length bs.
Proof.
  cbv [colL]; cbn [fst snd].
  revert a; induction bs; intros; [ reflexivity | ].
  cbn [colL']. simpl_ident. repeat destruct_pair_let.
  simpl_ident. cbn [fst snd length].
  rewrite IHbs. reflexivity.
Qed.

Hint Rewrite @colL_length using solve [length_hammer] : push_length.

Lemma addVCorrect (cin : bool) (n : nat) (a b : Vector.t bool n) :
  addLWithCinV cin a b =
  (N2Bv_sized (n+1) (Bv2N a + Bv2N b + (N.b2n cin))).
Proof.
  apply Bv2N_inj. rewrite Bv2N_N2Bv_sized.
  (* prove bounds side condition *)
  2:{
    pose proof (Bv2N_upper_bound _ a).
    pose proof (Bv2N_upper_bound _ b).
    rewrite <-!Nshiftl_equiv_nat in *.
    rewrite N.shiftl_1_l in *.
    rewrite PeanoNat.Nat.add_1_r.
    rewrite Nat2N.inj_succ, N.pow_succ_r by lia.
    destruct cin; cbv [N.b2n]; lia. }
  rewrite !Bv2N_list_bits_to_nat.
  rewrite <-addLCorrect by (rewrite !to_list_length; reflexivity).
  cbv [addLWithCinV adderWithGrowthV unsignedAdderV
       addLWithCinL adderWithGrowthL unsignedAdderL].
  rewrite colV_colL with (d:=false). simpl_ident.
  repeat destruct_pair_let. simpl_ident.
  autorewrite with push_to_list.
  reflexivity.
Qed.

(* A quick sanity check of the Xilinx adder with carry in and out *)
Example xilinx_add_17_52:
  xilinxAdderWithCarry
    (false, (N2Bv_sized 8 17, N2Bv_sized 8 52)) =
  (N2Bv_sized 8 69, false).
Proof. vm_compute. reflexivity. Qed.

(* A quick sanity check of the Xilinx adder with no bit-growth *)
Example xilinx_no_growth_add_17_52:
  xilinxAdder (N2Bv_sized 8 17) (N2Bv_sized 8 52) =
  (N2Bv_sized 8 69).
Proof. reflexivity. Qed.

(* A proof that the the Xilinx full-adder is correct. *)
Lemma xilinxFullAdder_behaviour :
  forall (a : bool) (b : bool) (cin : bool),
    xilinxFullAdder (cin, (a, b))
    = (xorb cin (xorb a b),
       (a && b) || (b && cin) || (a && cin)).
Proof.
  intros.
  unfold fst.
  simpl.
  case a, b, cin.
  all : reflexivity.
Qed.
