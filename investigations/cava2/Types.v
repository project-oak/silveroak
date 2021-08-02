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

Require Import Lia.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Cava.Util.Vector.

Inductive type :=
| Unit : type
| Bit  : type
| Vec  : type -> nat -> type
| Pair : type -> type -> type
.

Notation BitVec n := (Vec Bit n).

Definition eq_dec_type (x y: type): {x = y} + {x <> y}.
Proof.
  decide equality.
  apply Nat.eq_dec.
Defined.

Fixpoint denote_type (t: type) :=
  match t with
  | Unit => unit
  | Bit => bool
  | Vec t n => list (denote_type t)
  | Pair x y => (denote_type x * denote_type y)%type
  end.

Fixpoint eqb {t}: denote_type t -> denote_type t -> bool :=
  match t return denote_type t -> denote_type t -> bool with
  | Unit => fun _ _ => true
  | Bit => fun x y => Bool.eqb x y
  | Vec t n => fun x y =>
    fold_right andb true (map (fun '(x,y) => eqb (t:=t) x y) (combine x y))
  | Pair x y => fun '(x1,y1) '(x2,y2) => andb (eqb x1 x2) (eqb y1 y2)
  end.

(* *)
Fixpoint denote1_type (t: type) :=
  match t with
  | Unit => unit
  | Bit => bool
  | Vec t n =>
    match t with
    | Bit => N
    | _ => list (denote1_type t)
    end
  | Pair x y => (denote1_type x * denote1_type y)%type
  end.

Fixpoint denote1_to_denote {t} : denote1_type t -> denote_type t :=
  match t return denote1_type t -> denote_type t with
  | Vec t n =>
    let f := denote1_to_denote in
    match t as t1
      return ((denote1_type t1 -> denote_type t1)
              -> denote1_type (Vec t1 n) -> denote_type (Vec t1 n))
    with
    | Bit => fun _ x =>
      let v := N2Bv_sized n x in Vector.to_list v
    | _ => fun f x => map f x
    end f
  | Pair x y => fun '(x,y) => (denote1_to_denote x, denote1_to_denote y)
  | _ => id
  end.

Fixpoint denote_to_denote1 {t} : denote_type t -> denote1_type t :=
  match t return denote_type t -> denote1_type t with
  | Vec t n =>
    let f := denote_to_denote1 in
    match t as t1
      return ((denote_type t1 -> denote1_type t1)
              -> denote_type (Vec t1 n) -> denote1_type (Vec t1 n))
    with
    | Bit => fun _ x => Bv2N (Vector.of_list x)
    | _ => fun f x => map f x
    end f
  | Pair x y => fun '(x,y) => (denote_to_denote1 x, denote_to_denote1 y)
  | _ => id
  end.

Definition absorb_any (x y: type) :=
  match x, y with
  | Unit, x => x
  | x, Unit => x
  | _, _ => Pair x y
  end.

Fixpoint ntuple t n : type :=
  match n with
  | O => t
  | S n => Pair t (ntuple t n)
  end.

Fixpoint default {t: type} : denote_type t :=
  match t return denote_type t with
  | Unit => tt
  | Bit => false
  | Vec t1 n => List.repeat default n
  | Pair x y => (@default x, @default y)
  end.

Fixpoint default1 {t: type} : denote1_type t :=
  match t return denote1_type t with
  | Unit => tt
  | Bit => false
  | Vec t1 n =>
    match t1 return denote1_type t1 -> denote1_type (Vec t1 n) with
    | Bit => fun _ => 0%N
    | _ => fun d => List.repeat d n
    end default1
  | Pair x y => (@default1 x, @default1 y)
  end.

Fixpoint vector_as_tuple n t {struct n}
  : denote_type (Vec t (S n)) -> denote_type (ntuple t n) :=
  match n with
  | O => fun x => hd default x
  | S n' => fun ls =>
    (hd default ls, vector_as_tuple _ _ (tl ls))
  end.

Definition vector_as_tuple1 n t (x: denote1_type (Vec t (S n)))
  : denote_type (ntuple t n) :=
  vector_as_tuple _ _ (denote1_to_denote x).

(* Section test. *)
(*   Import ListNotations. *)
(*   Compute (vector_as_tuple1 _ _ ([0;1;2]:denote1_type (Vec (BitVec 3) 3)))%N. *)
(* End test. *)

Declare Scope circuit_type_scope.
Delimit Scope circuit_type_scope with circuit_type.
Open Scope circuit_type_scope.
Notation "[ ]" := Unit (format "[ ]") : circuit_type_scope.
Notation "[ x ]" := (Pair x Unit) : circuit_type_scope.
Notation "[ x ; y ; .. ; z ]" := (Pair x (Pair y .. (Pair z Unit) ..)) : circuit_type_scope.
Notation "x ** y" := (Pair x y)(at level 60, right associativity) : circuit_type_scope.
Notation "x ++ y" := (absorb_any x y) (at level 60, right associativity): circuit_type_scope.

