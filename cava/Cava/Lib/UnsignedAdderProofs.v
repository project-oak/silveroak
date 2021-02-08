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

Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Vectors.Vector.
Import VectorNotations.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.MonadLaws.
Import MonadNotation.
Open Scope monad_scope.
Open Scope type_scope.

Require Import coqutil.Tactics.Tactics.
Require Import Coq.micromega.Lia.

Require Import Cava.BitArithmetic Cava.ListUtils Cava.VectorUtils Cava.Tactics.
Require Import Cava.Lib.FullAdder.
Require Import Cava.Lib.UnsignedAdders.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.CombinationalMonad.
Require Import Cava.Acorn.Combinators.
Require Import Cava.Acorn.Identity.
Require Import Cava.Acorn.MonadFacts.

Local Open Scope N_scope.

(* First prove the full-adder correct. *)

Lemma fullAdder_correct (cin a b : bool) :
  semantics (fullAdder ([cin], ([a], [b]))) =
  let sum := N.b2n a + N.b2n b + N.b2n cin in
  ([N.testbit sum 0], [N.testbit sum 1]).
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

Lemma semantics_bind {A B} (f : ident A) (g : A -> ident B) :
  semantics (x <- f;; g x) = semantics (g (semantics f)).
Proof. reflexivity. Qed.

Lemma addLCorrect (cin : bool) (a b : list bool) :
  length a = length b ->
  match semantics (addLWithCinL [cin] [a] [b]) with
    | [bitAddition] => list_bits_to_nat bitAddition =
                      list_bits_to_nat a + list_bits_to_nat b + N.b2n cin
    | _ => False
  end.
Proof.
  cbv zeta. cbv [addLWithCinL adderWithGrowthL unsignedAdderL colL].
  cbn [fst snd].
  (* get rid of pair-let because it will cause problems in the inductive case *)
  simpl_ident. repeat destruct_pair_let.

  (* TODO(jadep) : repair this proof *)
(*
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
  rewrite <-app_comm_cons. cbv [semantics] in *.
  cbn [unIdent] in *. rewrite list_bits_to_nat_cons.

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
*)
Admitted.

(* Correctness of the vector based adder. *)

Lemma Bv2N_resize m n (Hmn : n = m) (v : t bool n) :
  Bv2N v = Bv2N (VectorUtils.resize_default false m v).
Proof.
  subst. rewrite VectorUtils.resize_default_id.
  reflexivity.
Qed.

Lemma colV_colL {A B C} {n} circuit inputs d :
  @colV _ CircuitSemantics A B C n circuit inputs =
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
    simpl_ident. repeat destruct_pair_let.
    simpl_ident. rewrite IHbs. clear IHbs.
    simpl_ident. cbn [fst snd of_list length].
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

Lemma colL_length {A B C} circuit a bs :
  length (fst (semantics (@colL ident _ A B C circuit (a,bs))))
  = length bs.
Proof.
  cbv [colL]; cbn [fst snd].
  revert a; induction bs; intros; [ reflexivity | ].
  cbn [colL'].
  repeat first [ rewrite semantics_bind
               | rewrite semantics_ret
               | destruct_pair_let ].
  cbn [fst snd length].
  rewrite IHbs. reflexivity.
Qed.

Hint Rewrite @colL_length using solve [length_hammer] : push_length.

Ltac simpl_monad :=
  repeat first [ rewrite semantics_bind
               | rewrite semantics_ret
               | destruct_pair_let
               | progress autorewrite with monadlaws
               | progress cbn [fst snd] ].

Lemma addVCorrect (cin : bool) (n : nat) (a b : Vector.t bool n) :
  semantics (addLWithCinV [cin] (peel [a]) (peel [b])) =
  peel 
       [N2Bv_sized (n+1) (Bv2N a + Bv2N b + (N.b2n cin))].
Proof.
  cbv zeta. rewrite !Bv2N_list_bits_to_nat.
  (* TODO(jadep) : repair this proof *)
  (*
  rewrite <-addLCorrect by (rewrite !to_list_length; reflexivity).
  cbv [addLWithCinV adderWithGrowthV unsignedAdderV
       addLWithCinL adderWithGrowthL unsignedAdderL].
  rewrite colV_colL with (d:=false).
  simpl_monad. autorewrite with push_to_list.
  reflexivity.
   *)
Admitted.

Local Close Scope N_scope.

