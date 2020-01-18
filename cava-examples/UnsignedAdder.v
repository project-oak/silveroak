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
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
Require Import Coq.Lists.List Coq.Bool.Bool.
From Coq Require Import ZArith.
From Coq Require Import Numbers.BinNums.
From Coq Require Import ZArith.Zdigits.
Require Import Lia.
Import ListNotations.

Scheme Equality for list.

Require Import Hask.Control.Monad.

Require Import Cava.
Require Import FullAdder.

Local Open Scope list_scope.
Local Open Scope monad_scope.

(* An unsigned addder which takes two size N bit-vectors and a carry in
   and returns a sized N+1 result which is the addition of the two
   input vectors and carry in.
*)

Definition unsignedAdder {m bit} `{Cava m bit} := col fullAdderFC.

(* A module definition for an 8-bit adder for SystemVerilog netlist
   generation.
*)

Definition adder8Top {m t} `{CavaTop m t} :=
  setModuleName "adder8" ;;
  a <- inputVectorTo0 8 "a" ;
  b <- inputVectorTo0 8 "b" ;
  cin <- inputBit "cin" ;
  sum_cout <- unsignedAdder cin (combine a b) ;
  let sum := fst sum_cout in
  let cout := snd sum_cout in
  outputVectorTo0 sum "sum" ;;
  outputBit "cout" cout.

Definition adder8Netlist := makeNetlist adder8Top.

Definition nat2bool (n : nat) : bool :=
  match n with
  | 0 => false
  | _ => true
  end.

(*
Definition toVec := map nat2bool.

Definition bool2nat (b : bool) : nat :=
  match b with
  | false => 0
  | true => 1
  end.

Definition fromVec := map bool2nat.

Definition v1 := [0;1;0;0;0;0;0;0].
Definition v2 := [1;0;0;0;0;0;0;0].


Definition eval_unsignedAdder a b :=
  let sum_carry := combinational (unsignedAdder false (combine (toVec a) (toVec b))) in
  let sum := fst sum_carry in
  let carry := snd sum_carry in
  (fromVec sum, bool2nat carry).

Compute (eval_unsignedAdder v1 v2).

Definition v3 := [1;1;1;1;1;1;1;1].
Definition v4 := [1;0;0;0;0;0;0;0].

Compute (eval_unsignedAdder v3 v4).

Definition v5 := [1;1;1;1;1;1;1;1].
Definition v6 := [1;1;1;1;1;1;1;1].

Compute (eval_unsignedAdder v5 v6).

Definition bool_to_z (b : bool) : nat :=
  match b with
  | false => 0
  | true => 1
  end.

Fixpoint vec_to_z (l : list bool) : nat :=
  match l with
  | [] => 0
  | x::xs => bool_to_z x + 2 * vec_to_z xs
  end.

Compute (vec_to_z (toVec v1)).
Compute (vec_to_z (toVec v2)).
Compute (vec_to_z (toVec v3)).
Compute (vec_to_z (toVec v4)).
Compute (vec_to_z (toVec v5)).
Compute (vec_to_z (toVec v6)).
*)

Definition add (a : nat) (b : nat) : nat
  := a + b.

Lemma add_proof : forall a b,
                  add a b = a + b.
Proof.
  auto.
Qed.

Definition addz (a : Z) (b : Z) : Z
  := a + b.

Lemma addz_proof : forall a b,
                   addz a b = (a + b)%Z.
Proof.
  auto.
Qed.

Definition x6 : N := Npos (xO (xI xH)).
Compute x6.

Definition x0 : N := N0.
Compute x0.

Definition x5 : N := Npos (xI (xO xH)).
Compute x5.

Fixpoint strip_false (l : list bool) : list bool :=
  match l with
  | false::xs => strip_false xs
  | _ => l
  end.

Fixpoint bv_to_n_pos (l : list bool) (n : positive) : positive :=
  match l with
  | [] => n
  | x::xs => match x with
             | false => bv_to_n_pos xs (xO n)
             | true => bv_to_n_pos xs (xI n)
             end
  end.

Definition bv_to_n (l : list bool) : N :=
  match strip_false (rev l) with
  | [] => N0
  | x::xs => Npos (bv_to_n_pos xs xH)
  end.

Definition v1b := [false;true;true;false; false;false;false].
Definition v1bn := bv_to_n v1b.
Compute v1bn.

Definition v2b := [false;true;true;false; false;true;false].
Definition v2bn := bv_to_n v2b.
Compute v2bn.

Definition v3b := [false;false;false;false; false;false;false].
Definition v3bn := bv_to_n v3b.
Compute v3bn.

Definition add8 {m t} `{CavaTop m t} ab :=
  sum_carry <- unsignedAdder false ab;
  let sum := fst sum_carry in
  let carry := snd sum_carry in
  return_ (sum ++ [carry]).

(*
Definition add8bv {m t} `{CavaTop m t} abbv  :=
  let a := to_list (fst abbv) in
  let b := to_list (snd abbv) in
  sum_carry <- unsignedAdder false (combine a b);
  let sum := fst sum_carry in
  let carry := snd sum_carry in
  return_ (of_list (sum ++ [carry])).
*)

(* 

Lemma add8_bheaviour : forall (ab : list (bool * bool)),
                       bv_to_n (combinational (add8 ab)) =
                       ((bv_to_n (map fst ab)) + (bv_to_n (map snd ab)))%N.
Proof.
  induction ab.
  auto.
  unfold combinational.
  unfold add8.
  unfold fst.
  unfold unsignedAdder.
  unfold fullAdderFC.
  destruct x.
 
  


  unfold vec_to_z.
  simpl.
  unfold combinational.
  unfold fst.
  destruct ab.
  simpl.
  unfold bool_to_z.
  reflexivity.
  
 *)

