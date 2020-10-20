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

(* Lemma about how to decompose a list of vectors. *)
Lemma list_bits_to_nat_cons b bs :
  list_bits_to_nat (b :: bs) = (N.b2n b + 2 * (list_bits_to_nat bs))%N.
Proof.
  cbv [list_bits_to_nat].
  cbn [Vector.of_list Ndigits.Bv2N].
  destruct b; cbn [N.b2n].
  all: rewrite ?N.succ_double_spec, ?N.double_spec.
  all:lia.
Qed.

Hint Rewrite @bind_of_return @bind_associativity
     using solve [typeclasses eauto] : monadlaws.

(* Correctness of the list based adder. *)

Lemma addLCorrect (cin : bool) (a b : list bool) :
  length a = length b ->
  let bitAddition := combinational (addLWithCinL cin a b) in
  list_bits_to_nat bitAddition =
  list_bits_to_nat a + list_bits_to_nat b + N.b2n cin.
Proof.
  cbv zeta. cbv [addLWithCinL adderWithGrowthL unsignedAdderL].
  (* get rid of pair-let because it will cause problems in the inductive case *)
  erewrite ident_bind_Proper_ext with (g := fun x => ret (fst x ++ [snd x]));
    [ | intros; destruct_products; reflexivity ].
  (* start induction; eliminate cases where length b <> length a and solve base
     case immediately *)
  revert dependent cin. revert dependent b.
  induction a; (destruct b; cbn [length]; try lia; [ ]); intros;
    [ destruct cin; reflexivity | ].

(* Need to define/prove equivalent of col_cons.
  (* inductive case only now; simplify *)
  rewrite !list_bits_to_nat_cons. col_cons.
  cbv [prod_curry]. autorewrite with monadlaws.

  (* use fullAdder_correct to replace fullAdder call with addition + testbit *)
  rewrite combinational_bind.
  rewrite fullAdder_correct. cbv zeta.
  (cbn match beta). autorewrite with monadlaws.

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
*)
Abort.

(* Correctness of the vector based adder. *)

Lemma addVCorrect (cin : bool) (n : nat) (a b : Vector.t bool n) :
  let bitAddition := combinational (addLWithCinV cin a b) in
  Bv2N bitAddition =
  Bv2N a + Bv2N b + (N.b2n cin).
Abort.

Local Close Scope N_scope.

