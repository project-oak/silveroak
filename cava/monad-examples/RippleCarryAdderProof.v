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
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
Require Import Omega.
Import ListNotations.

Require Import ExtLib.Structures.Monads.

Require Import ExtLib.Structures.MonadLaws.
Require Import coqutil.Tactics.Tactics.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Morphisms.

Require Import Cava.Cava.
Require Import Cava.Monad.CavaMonad.
Require Import Cava.Monad.MonadFacts.
Require Import MonadExamples.FullAdder.

Require Import ExtLib.Structures.MonadLaws.
Require Import coqutil.Tactics.Tactics.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Morphisms.

(******************************************************************************)
(* Prove the ripple-carry adder correct using list based col.                 *)
(******************************************************************************)

Local Open Scope N_scope.

Lemma ripple_adder_correct (cin : bool) (a b : list bool) :
  length a = length b ->
  let bitAddition := combinational (adderWithGrowth (cin, (a, b))) in
  list_bits_to_nat bitAddition =
  list_bits_to_nat a + list_bits_to_nat b + (N.b2n cin).
Proof.
  cbv zeta. cbv [adderWithGrowth adder adder'].
  (* get rid of pair-let because it will cause problems in the inductive case *)
  erewrite ident_bind_Proper_ext with (g := fun x => ret (fst x ++ [snd x]));
    [ | intros; destruct_products; reflexivity ].
  (* start induction; eliminate cases where length b <> length a and solve base
     case immediately *)
  revert dependent cin. revert dependent b.
  induction a; (destruct b; cbn [length]; try lia; [ ]); intros;
    [ destruct cin; reflexivity | ].

  (* inductive case only now; simplify *)
  rewrite !list_bits_to_nat_cons, col_cons.
  cbn [combine fst snd below_cons prod_uncurry below_cons'].
  cbv [prod_curry]. autorewrite with monadlaws.

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