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

(* simple_denote_type denotes all 'Vec's as lists *)
Fixpoint simple_denote_type (t: type) :=
  match t with
  | Unit => unit
  | Bit => bool
  | Vec t n => list (simple_denote_type t)
  | Pair x y => (simple_denote_type x * simple_denote_type y)%type
  end.

Fixpoint eqb_simple {t}: simple_denote_type t -> simple_denote_type t -> bool :=
  match t return simple_denote_type t -> simple_denote_type t -> bool with
  | Unit => fun _ _ => true
  | Bit => fun x y => Bool.eqb x y
  | Vec t n => fun x y =>
    fold_right andb true (map (fun '(x,y) => eqb_simple (t:=t) x y) (combine x y))
  | Pair x y => fun '(x1,y1) '(x2,y2) => andb (eqb_simple x1 x2) (eqb_simple y1 y2)
  end.

(* simple_denote_type denotes 'BitVec's as N *)
Fixpoint denote_type (t: type) :=
  match t with
  | Unit => unit
  | Bit => bool
  | Vec t n =>
    match t with
    | Unit => unit
    | Bit => N
    | _ => list (denote_type t)
    end
  | Pair x y => (denote_type x * denote_type y)%type
  end.

Fixpoint eqb {t}: denote_type t -> denote_type t -> bool :=
  match t return denote_type t -> denote_type t -> bool with
  | Unit => fun _ _ => true
  | Bit => fun x y => Bool.eqb x y
  | Vec t n =>
    let eqb_f := eqb (t:=t) in
    match t return (denote_type t -> denote_type t -> bool) -> denote_type (Vec t n) -> denote_type (Vec t n) -> bool with
    | Unit => fun _ _ _ => true
    | Bit => fun _ => N.eqb
    | _ => fun eqb x y =>
      fold_right andb true (map (fun '(x,y) => eqb x y) (combine x y))
    end eqb_f
  | Pair x y => fun '(x1,y1) '(x2,y2) => andb (eqb x1 x2) (eqb y1 y2)
  end.

Fixpoint denote_to_simple_denote {t} : denote_type t -> simple_denote_type t :=
  match t return denote_type t -> simple_denote_type t with
  | Vec t n =>
    let f := denote_to_simple_denote in
    match t as t1
      return ((denote_type t1 -> simple_denote_type t1)
              -> denote_type (Vec t1 n) -> simple_denote_type (Vec t1 n))
    with
    | Unit => fun _ _ => List.repeat tt n
    | Bit => fun _ x =>
      let v := N2Bv_sized n x in Vector.to_list v
    | _ => fun f x => map f x
    end f
  | Pair x y => fun '(x,y) => (denote_to_simple_denote x, denote_to_simple_denote y)
  | _ => id
  end.

Fixpoint simple_denote_to_denote {t} : simple_denote_type t -> denote_type t :=
  match t return simple_denote_type t -> denote_type t with
  | Vec t n =>
    let f := simple_denote_to_denote in
    match t as t1
      return ((simple_denote_type t1 -> denote_type t1)
              -> simple_denote_type (Vec t1 n) -> denote_type (Vec t1 n))
    with
    | Unit => fun _ _ => tt
    | Bit => fun _ x => Bv2N (Vector.of_list x)
    | _ => fun f x => map f x
    end f
  | Pair x y => fun '(x,y) => (simple_denote_to_denote x, simple_denote_to_denote y)
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

Fixpoint simple_default {t: type} : simple_denote_type t :=
  match t return simple_denote_type t with
  | Unit => tt
  | Bit => false
  | Vec t1 n => List.repeat simple_default n
  | Pair x y => (@simple_default x, @simple_default y)
  end.

Fixpoint default {t: type} : denote_type t :=
  match t return denote_type t with
  | Unit => tt
  | Bit => false
  | Vec t1 n =>
    match t1 return denote_type t1 -> denote_type (Vec t1 n) with
    | Unit => fun _ => tt
    | Bit => fun _ => 0%N
    | _ => fun d => List.repeat d n
    end default
  | Pair x y => (@default x, @default y)
  end.

Definition via_simple {a b} (f: simple_denote_type a -> simple_denote_type b)
  : denote_type a -> denote_type b
  := fun x => simple_denote_to_denote (f (denote_to_simple_denote x)).
Definition via_simple2 {a b c} (f: simple_denote_type a -> simple_denote_type b -> simple_denote_type c)
  : denote_type a -> denote_type b -> denote_type c
  := fun x y => simple_denote_to_denote (f (denote_to_simple_denote x) (denote_to_simple_denote y)).

Fixpoint vector_as_tuple n t {struct n}
  : simple_denote_type (Vec t (S n)) -> simple_denote_type (ntuple t n) :=
  match n with
  | O => fun x => hd simple_default x
  | S n' => fun ls =>
    (hd simple_default ls, vector_as_tuple _ _ (tl ls))
  end.

Definition vector_as_tuple1 n t (x: denote_type (Vec t (S n)))
  : simple_denote_type (ntuple t n) :=
  vector_as_tuple _ _ (denote_to_simple_denote x).

Declare Scope circuit_type_scope.
Delimit Scope circuit_type_scope with circuit_type.
Open Scope circuit_type_scope.
Notation "[ ]" := Unit (format "[ ]") : circuit_type_scope.
Notation "[ x ]" := (Pair x Unit) : circuit_type_scope.
Notation "[ x ; y ; .. ; z ]" := (Pair x (Pair y .. (Pair z Unit) ..)) : circuit_type_scope.
Notation "x ** y" := (Pair x y)(at level 60, right associativity) : circuit_type_scope.
Notation "x ++ y" := (absorb_any x y) (at level 60, right associativity): circuit_type_scope.


Inductive denote_rel: type -> Type -> Type :=
| denote_Unit: denote_rel Unit unit
| denote_Bit: denote_rel Bit bool
| denote_Vec_of_Unit: forall n,
    denote_rel (Vec Unit n) unit
| denote_Vec_of_Bit: forall n,
    denote_rel (Vec Bit n) N
| denote_Vec_of_Vec: forall t T n m,
    denote_rel (Vec t m) T ->
    denote_rel (Vec (Vec t m) n) (list T)
| denote_Vec_of_Pair: forall t1 t2 T n,
    denote_rel (Pair t1 t2) T ->
    denote_rel (Vec (Pair t1 t2) n) (list T)
| denote_Pair: forall x y X Y,
    denote_rel x X -> denote_rel y Y -> denote_rel (Pair x y) (X * Y).

Lemma denote_rel_to_denote_type: forall t T, denote_rel t T -> T = denote_type t.
Proof. induction 1; subst; try reflexivity. Qed.

Fixpoint denote_rel_of_denote_type(t: type): denote_rel t (denote_type t) :=
  match t with
  | Unit => denote_Unit
  | Bit => denote_Bit
  | Vec t1 n =>
    match t1
      return denote_rel t1 (denote_type t1) -> denote_rel (Vec t1 n) (denote_type (Vec t1 n))
    with
    | Unit => fun r => denote_Vec_of_Unit n
    | Bit => fun r => denote_Vec_of_Bit n
    | Vec t2 m => fun r => denote_Vec_of_Vec t2 (denote_type (Vec t2 m)) n m r
    | Pair x y => fun r  => denote_Vec_of_Pair _ _ _ n r
    end (denote_rel_of_denote_type t1)
  | Pair x y => denote_Pair x y _ _ (denote_rel_of_denote_type x) (denote_rel_of_denote_type y)
  end.

Existing Class denote_rel.
Existing Instance denote_rel_of_denote_type.

Fixpoint cast{x X}(dx: denote_rel x X){struct dx}: X -> denote_type x :=
  match dx with
  | denote_Unit => id
  | denote_Bit => id
  | denote_Vec_of_Unit _ => id
  | denote_Vec_of_Bit _ => id
  | denote_Vec_of_Vec t T n m dV => List.map (cast dV)
  | denote_Vec_of_Pair t1 t2 T n dt => List.map (cast dt)
  | denote_Pair x y X Y d1 d2 => fun '(e1, e2) => (cast d1 e1, cast d2 e2)
  end.
