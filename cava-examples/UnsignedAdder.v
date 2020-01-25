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
(* From Coq Require Import Numbers.BinNums. *)
(* From Coq Require Import ZArith.Zdigits. *)
Require Import Lia.
Import ListNotations.

Scheme Equality for list.

Require Import Hask.Control.Monad.

Require Import Cava.
Require Import FullAdder.
Require Import FullAdderNat.
Require Import BitVector.

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

Definition toVec := map nat2bool.

Definition bool2nat (b : bool) : nat :=
  match b with
  | false => 0
  | true => 1
  end.


Definition adder {m bit} `{Cava m bit} cin ab :=
  sum_carry <- unsignedAdder cin ab ;
  return_ (fst sum_carry ++ [snd sum_carry]).


Definition fromVec := map bool2nat.

(****************************************************************************)

Definition v1 := [0;1;0;0;0;0;0;0].
Definition v2 := [1;0;0;0;0;0;0;0].

Definition eval_unsignedAdder a b :=
  fromVec (combinational (adder false (combine (toVec a) (toVec b)))).

Example v1_plus_v2 : eval_unsignedAdder v1 v2 = [1; 1; 0; 0; 0; 0; 0; 0; 0].
Proof. reflexivity. Qed.

(****************************************************************************)

Definition v0 : list nat := [].

Example v0_plus_v0 : eval_unsignedAdder v0 v0 = [0].
Proof. reflexivity. Qed.

(****************************************************************************)

Definition v3 := [1;1;1;1;1;1;1;1].
Definition v4 := [1;0;0;0;0;0;0;0].

Example v3_plus_v4 : eval_unsignedAdder v3 v4 = [0; 0; 0; 0; 0; 0; 0; 0; 1].
Proof. reflexivity. Qed.

(****************************************************************************)

Definition v5 := [1;1;1;1;1;1;1;1].
Definition v6 := [1;1;1;1;1;1;1;1].

Example v5_plus_v6 : eval_unsignedAdder v5 v6 = [0; 1; 1; 1; 1; 1; 1; 1; 1].
Proof. reflexivity. Qed.

(****************************************************************************)

Definition bool_to_n (b : bool) : nat :=
  match b with
  | false => 0
  | true => 1
  end.

(*

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

*)

Definition addN {m t} `{CavaTop m t} ab :=
  sum_carry <- unsignedAdder false ab;
  let sum := fst sum_carry in
  let carry := snd sum_carry in
  return_ (sum ++ [carry]).


Lemma addN_bheaviour : forall (ab : list (bool * bool)), 
                       bits_to_nat (combinational (addN ab)) =
                       (bits_to_nat (map fst ab)) + (bits_to_nat (map snd ab)).
Proof.
Abort.
  

  

  


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
Theorem test : forall n:nat, n + 1 > n.
Proof.
  induction n. 
  auto.
Qed.


Lemma add1_bheaviour : forall (ab : list (bool * bool)), length ab = 1 ->
                       vec_to_n (combinational (addN ab)) =
                       (vec_to_n (map fst ab)) + (vec_to_n (map snd ab)).
Proof.
  intros.
  unfold combinational. 
  unfold fst.
  unfold addN.
  unfold unsignedAdder.
  destruct ab.
  simpl.
  auto.
  unfold col.
  unfold below.
  unfold fullAdderFC.
  unfold fst in *.

  destruct ab.
  simpl.
  auto.

Lemma add8_bheaviour : forall (ab : list (bool * bool)), length ab > 1 ->
                       vec_to_n (combinational (add8 ab)) =
                       (vec_to_n (map fst ab)) + (vec_to_n (map snd ab)).
Proof.
  intros.
  induction ab.
  auto.
  
 
  induction ab. 
  auto.
  induction ab.
  simpl.
  unfold bool_to_n.
  simpl.
  unfold fst in *.
  unfold snd in *.
  simpl.
  destruct a.
  destruct b.
  destruct b0.
  simpl.
  auto.
  simpl.
  auto.
  destruct b0.
  simpl.
  auto.
  simpl.
  auto.
  

  rewrite -> IHab.
  induction ab.
  
  unfold combinational. 
  unfold fst.
  unfold add8.
  unfold unsignedAdder.
  unfold fullAdderFC. 
  unfold map.
  unfold snd. 
  unfold vec_to_n. 
  unfold bool_to_n.


  


  unfold vec_to_z.
  simpl.
  unfold combinational.
  unfold fst.
  destruct ab.
  simpl.
  unfold bool_to_z.
  reflexivity.
  
 *)

