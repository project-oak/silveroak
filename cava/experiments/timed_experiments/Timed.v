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

(** Experiments with timed proofs *)

From Coq Require Import Bool.Bool.

From Coq Require Import Lists.List.
From Coq Require Import ZArith.
From Coq Require Import btauto.Btauto.
Require Import Program.Basics.
Import ListNotations.
Local Open Scope program_scope.
Local Open Scope list_scope.

Definition Trace (t: Type) := list t.

Fixpoint zipWith {A : Type} {B : Type} {C: Type} f (l : list A) (l' : list B) : list C :=
match l,l' with
  | x::tl, y::tl' => (f x y)::(zipWith f tl tl')
  | _, _ => nil
end.

(** simple expression type *)
Inductive expr: Type :=
| Input: Trace bool -> expr
| Not: expr -> expr
| And: expr -> expr -> expr
| Delay: expr -> expr.

Fixpoint runExpr (e: expr) :=
    match e with
    | Input t => t
    | Not e => map negb (runExpr e)
    | And e1 e2 => zipWith (andb) (runExpr e1) (runExpr e2)
    | Delay e => false :: (runExpr e)
    end.

Definition nand a b := Not (And a b).
Definition xor a b := 
    nand (nand a (nand a b)) (nand b (nand a b)).

(* for combinational expressions, set inputs to singleton lists, 
and take the head of the result trace*)
Definition combinational2 e a b: _ :=
    hd_error(runExpr (e
                (Input (a :: nil)) 
                (Input (b :: nil))
                )).

Lemma xor_is_xorb : forall a b, combinational2 xor a b = Some (xorb a b).
Proof.
    intros a b.
    unfold combinational2.
    simpl.
    f_equal.
    btauto.
Qed.

(* xor with delays *)
Definition pipelined_xor a' b' :=
    let a := Input a' in
    let b := Input b' in
    nand
        (Delay (nand (Delay a) (Delay (nand a b))))
        (Delay (nand (Delay b) (Delay (nand a b)))).

Eval simpl in tl(tl(runExpr (pipelined_xor
        ( [false;false;true;true])
        ( [false;true;false;true])))).
Eval simpl in zipWith xorb
            ( [false;false;true;true])
            ( [false;true;false;true]).

Lemma pipelined_xor_delay_is_2: 
    forall (i : Trace (bool * bool)),
    length (runExpr (pipelined_xor (map fst i) (map snd i))) = length i + 2.
Proof.
    intros.
    cbv.
    induction i.
    reflexivity.
    rewrite IHi.
    reflexivity.
Qed.

Lemma pipelined_xor_is_xorb_delayed2_once: 
    forall x y,
    tl(tl(runExpr (pipelined_xor [x] [y])))  = zipWith xorb [x] [y].
Proof.
    intros.
    subst.
    simpl.
    f_equal.
    btauto.
Qed.

Lemma lengths': forall {A}{B} (a:A) (b:B) (x: list A) (y: list B),
    length (a :: x) = length (b :: y) -> length x = length y.
Proof.
    intros.
    auto.
Qed.

(* proof that the "pipelined" xor is equivalent to xorb delayed by 2 cycles *)
Lemma pipelined_xor_is_xorb_delayed2:
    forall (x y : Trace bool),
    length x = length y ->
    tl(tl(runExpr (pipelined_xor x y))) = zipWith xorb x y.
Proof. 
    induction x.
    trivial.
    intros.
    unfold pipelined_xor.
    cbn [runExpr nand xor].
    destruct y.
    trivial.
    simpl.
    f_equal.
    btauto.
    simpl in IHx.
    rewrite IHx.
    reflexivity.
    auto.
Qed.






    
    





    

    




