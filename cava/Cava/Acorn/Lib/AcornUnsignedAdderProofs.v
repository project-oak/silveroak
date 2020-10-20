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

From Coq Require Import Bool.Bool.
From Coq Require Import NArith.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Vector.
From Coq Require Import Bool.Bvector.
Import VectorNotations.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.MonadLaws.
Import MonadNotation.
Open Scope monad_scope.
Open Scope type_scope.

Require Import coqutil.Tactics.Tactics.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Morphisms.

From Cava Require Import BitArithmetic.
Require Import Cava.Monad.MonadFacts.

From Cava Require Import Acorn.Acorn.
From Cava Require Import Acorn.Lib.AcornFullAdder.
From Cava Require Import Acorn.Lib.AcornUnsignedAdders.

Local Open Scope N_scope.

(* First prove the full-adder correct. *)

Lemma fullAdder_correct (cin a b : bool) :
  combinational (fullAdder (cin, (a, b))) =
  let sum := N.b2n a + N.b2n b + N.b2n cin in
  (N.testbit sum 0, N.testbit sum 1).
Proof. destruct cin, a, b; reflexivity. Qed.

(* Lemma about how to decompose a vector of bits. *)
Lemma Bv2N_cons n b (bs : t bool n) :
  Bv2N (b :: bs)%vector = (N.b2n b + 2 * (Bv2N bs))%N.
Proof.
  cbn [Bv2N]. destruct b; cbn [N.b2n].
  all: rewrite ?N.succ_double_spec, ?N.double_spec.
  all:lia.
Qed.

(* Lemma about how to decompose a list of bits. *)
Lemma list_bits_to_nat_cons b bs :
  list_bits_to_nat (b :: bs) = (N.b2n b + 2 * (list_bits_to_nat bs))%N.
Proof. apply Bv2N_cons. Qed.

Hint Rewrite @bind_of_return @bind_associativity
     using solve [typeclasses eauto] : monadlaws.

(* Correctness of the list based adder. *)

Lemma combinational_bind {A B} (f : ident A) (g : A -> ident B) :
  combinational (x <- f;; g x) = combinational (g (combinational f)).
Proof. reflexivity. Qed.

Lemma addLCorrect (cin : bool) (a b : list bool) :
  length a = length b ->
  let bitAddition := combinational (addLWithCinL cin a b) in
  list_bits_to_nat bitAddition =
  list_bits_to_nat a + list_bits_to_nat b + N.b2n cin.
Proof.
  cbv zeta. cbv [addLWithCinL adderWithGrowthL unsignedAdderL colL].
  cbn [fst snd].
  (* get rid of pair-let because it will cause problems in the inductive case *)
  erewrite ident_bind_Proper_ext with (g := fun x => ret (fst x ++ [snd x]));
    [ | intros; destruct_products; reflexivity ].
  (* start induction; eliminate cases where length b <> length a and solve base
     case immediately *)
  revert dependent cin. revert dependent b.
  induction a; (destruct b; cbn [length]; try lia; [ ]); intros;
    [ destruct cin; reflexivity | ].

  (* inductive case only now; simplify *)
  cbn [combine colL']. rewrite !list_bits_to_nat_cons.
  autorewrite with monadlaws.

  (* use fullAdder_correct to replace fullAdder call with addition + testbit *)
  rewrite combinational_bind.
  rewrite fullAdder_correct. cbv zeta.
  (cbn match beta). autorewrite with monadlaws.

  (* Now, use the _ext lemma to rearrange under the binder and match inductive
     hypothesis *)
  erewrite ident_bind_Proper_ext.
  2:{ intro y. rewrite (surjective_pairing y) at 1.
      autorewrite with monadlaws. cbn [fst snd].
      rewrite <-app_comm_cons. reflexivity. }

  (* pull cons out of the ret statement *)
  rewrite ident_bind_lift_app.
  rewrite combinational_bind, combinational_ret.
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
  Bv2N v = Bv2N (VectorUtils.resize_default false m v).
Proof.
  subst. rewrite VectorUtils.resize_default_id.
  reflexivity.
Qed.

Require Import Cava.Tactics.

Lemma to_list_cons {A n} a (v : t A n) :
  to_list (a :: v)%vector = a :: to_list v.
Proof. reflexivity. Qed.

Ltac destruct_pair_let_under_bind' :=
  lazymatch goal with
  | |- context [bind ?x ?f] =>
    let A := lazymatch type of f with
             | prod ?A _ -> _ => A end in
    let B := lazymatch type of f with
             | prod _ ?B -> _ => B end in
    lazymatch f with
    | (fun y =>
         match y with
         | @Datatypes.pair _ _ a b => ?e
         end) =>
      let g := constr:(fun (y : A * B) =>
                         let a := fst y in
                         let b := snd y in e) in
      erewrite (ident_bind_Proper_ext _ _ x f g)
    end
  end.

Ltac destruct_pair_let_under_bind :=
  destruct_pair_let_under_bind';
  [ | let x := fresh in
      intro x; destruct_pair_let;
      rewrite <-(surjective_pairing x);
      reflexivity ].

Lemma colV_colL {A B C} {n} circuit inputs d :
  @colV ident _ A B C n circuit inputs =
  (let inputL := (fst inputs, to_list (snd inputs)) in
   rL <- colL circuit inputL ;;
      let rV := VectorUtils.resize_default
                  d _ (Vector.of_list (fst rL)) in
      ret (rV, snd rL)).
Proof.
  cbv [colV colL]. destruct inputs as [a bs]. cbn [fst snd].
  revert a; induction bs; intros.
  { cbn [colL' colV' to_list fst snd].
    autorewrite with monadlaws; reflexivity. }
  { rewrite !to_list_cons. cbn [colL' colV'].
    autorewrite with monadlaws.
    destruct_pair_let_under_bind. cbv zeta.
    cbv [Monad_ident bind ret unIdent].
    rewrite IHbs. clear IHbs.
    cbv [Monad_ident bind ret unIdent].
    f_equal.
    repeat first [ progress cbn [fst snd]
                 | destruct_pair_let
                 | destruct_one_match ].
    cbn [fst snd of_list length].
    cbn [VectorUtils.resize_default].
    autorewrite with vsimpl.
    reflexivity. }
Qed.

Lemma Bv2N_list_bits_to_nat n (v : t bool n) :
  Bv2N v = list_bits_to_nat (to_list v).
Proof.
  induction v; intros; [ reflexivity | ].
  rewrite to_list_cons, Bv2N_cons, list_bits_to_nat_cons.
  lia.
Qed.

Lemma to_list_resize_default {A} n m (v : t A n) d :
  n = m ->
  to_list (VectorUtils.resize_default d m v) = to_list v.
Proof.
  intros; subst; rewrite VectorUtils.resize_default_id.
  reflexivity.
Qed.

Lemma to_list_append {A n m} (v1 : t A n) (v2 : t A m) :
  to_list (v1 ++ v2)%vector = to_list v1 ++ to_list v2.
Proof.
  revert v2; induction v1; [ reflexivity | ].
  intros. rewrite <-append_comm_cons.
  cbn [Nat.add]. rewrite !to_list_cons.
  rewrite <-app_comm_cons, IHv1.
  reflexivity.
Qed.

Lemma to_list_vcombine {A B n} (v1 : t A n) (v2 : t B n) :
  to_list (VectorUtils.vcombine v1 v2) = combine (to_list v1) (to_list v2).
Proof.
  induction n; intros.
  { eapply case0 with (v:=v1). eapply case0 with (v:=v2).
    reflexivity. }
  { rewrite (eta v1), (eta v2).
    cbn [VectorUtils.vcombine].
    rewrite !uncons_cons, !to_list_cons.
    cbn [combine]. rewrite IHn; reflexivity. }
Qed.

Lemma to_list_length {A n} (v : t A n) :
  length (to_list v) = n.
Proof.
  induction v; [ reflexivity | ].
  rewrite to_list_cons. cbn [length].
  congruence.
Qed.

Lemma colL_length {A B C} circuit inputs :
  length (fst (combinational (@colL ident _ A B C circuit inputs)))
  = length (snd inputs).
Proof.
  destruct inputs as [a bs]. cbv [colL]; cbn [fst snd].
  revert a; induction bs; intros; [ reflexivity | ].
  cbn [colL'].
  repeat first [ rewrite combinational_bind
               | rewrite combinational_ret
               | destruct_pair_let ].
  cbn [fst snd length].
  rewrite IHbs. reflexivity.
Qed.

Lemma to_list_nil {A} : to_list (Vector.nil A) = [].
Proof. reflexivity. Qed.

Hint Rewrite @colL_length @combine_length @to_list_length
     using solve [eauto] : push_length.
Ltac simpl_length :=
  repeat first [ progress autorewrite with push_length
               | progress cbn [fst snd] ].

Hint Rewrite @to_list_append  @to_list_vcombine
     @to_list_of_list_opp @to_list_nil @to_list_cons
     using solve [eauto] : push_to_list.
Hint Rewrite @to_list_resize_default
     using solve [simpl_length; lia] : push_to_list.

Ltac simpl_monad :=
  repeat first [ rewrite combinational_bind
               | rewrite combinational_ret
               | destruct_pair_let
               | progress autorewrite with monadlaws
               | progress cbn [fst snd] ].

Lemma addVCorrect (cin : bool) (n : nat) (a b : Vector.t bool n) :
  let bitAddition := combinational (addLWithCinV cin a b) in
  Bv2N bitAddition =
  Bv2N a + Bv2N b + (N.b2n cin).
Proof.
  cbv zeta. rewrite !Bv2N_list_bits_to_nat.
  rewrite <-addLCorrect by (rewrite !to_list_length; reflexivity).
  cbv [addLWithCinV adderWithGrowthV unsignedAdderV
       addLWithCinL adderWithGrowthL unsignedAdderL].
  rewrite colV_colL with (d:=false).
  simpl_monad. autorewrite with push_to_list.
  reflexivity.
Qed.

Local Close Scope N_scope.

