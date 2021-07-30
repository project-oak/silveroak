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
| Nat  : type
| Vec  : type -> nat -> type
| Pair : type -> type -> type
.

Notation BitVec n := (Vec Bit n).

Definition eq_dec_type (x y: type): {x = y} + {x <> y}.
Proof.
  decide equality.
  apply Nat.eq_dec.
Defined.

Section RefinedLists.
  Import ListNotations.

  Notation rlist A n := {l : list A | Datatypes.length l = n}.

  (* Do these exist somewhere *)
  Lemma empty_list_with_Sn_length_is_false
       : forall {t : Type} {n : nat} {x : list t},
         Datatypes.length x = S n -> x = [] -> False.
  Proof. intros; rewrite H0 in H; inversion H. Qed.

  Lemma append_push_list_length
       : forall {t : Type} {n : nat} {x0 : list t},
         Datatypes.length x0 = S n ->
         forall (x : t) (xs : list t), x0 = x :: xs -> Datatypes.length xs = n.
  Proof. intros; rewrite H0 in H; cbn in *; congruence. Qed.

  Definition hd_safe {t n} (ls: rlist t (S n)): (t * rlist t n) :=
    let (ls', Hlen) := ls in
    match ls' as ls'' return ls' = ls'' -> (t * rlist _ _) with
    | [] => fun Heq => False_rect _ (empty_list_with_Sn_length_is_false Hlen Heq)
    | x::xs => fun Heq => (x, exist _ xs (append_push_list_length Hlen x _ Heq))
    end eq_refl.

  Program Definition map {A B n} (f: A -> B) (ls: rlist A n): rlist B n :=
    let (ls', Hlen) := ls in List.map f ls'.
  Next Obligation.  rewrite map_length; reflexivity. Qed.

  (* Lemma _ (tl ls : rlist A (n - 1)) _)) _ *)

  Fixpoint ldrop {A} n (ls: list A): list A :=
    match n with
    | O => ls
    | S n' => ldrop n' (tl ls)
    end.

  Program Fixpoint drop {A n} (m: nat) (ls: rlist A n) {struct m}: rlist A (n - m) :=
    ldrop m ls.
  Next Obligation.
    revert m.

    induction ls.
    induction m.
    - reflexivity.
    - apply IHm.
    - induction m; [reflexivity| apply IHls].
  Qed.

  Definition slice {A n} (start len: nat)
      (ls: {l : list A | Datatypes.length l = n}):
      if len <=? n - start then {l : list A | Datatypes.length l = len}
      else unit :=
    let (ls', Hlen) := ls in
    if len <=? n - start then _ (drop start ls)
    else tt.
End.

End RefinedLists.

Fixpoint denote_type (t: type) :=
  match t with
  | Unit => unit
  | Bit => bool
  | Nat => nat
    (* Experience suggests to avoid vectors? What about refined lists - will the
    * prop size grow and be an issue with proof? *)
    (* One pro: Prop erasure in extraction means extracted terms are smaller
     * than vecs *)
  | Vec t n => {l: list (denote_type t) | List.length l = n}
  | Pair x y => (denote_type x * denote_type y)%type
  end.

(* *)
Fixpoint denote1_type (t: type) :=
  match t with
  | Unit => unit
  | Bit => bool
  | Nat => nat
  | Vec t n =>
    match t with
    | Bit => N
    | _ => {l: list (denote1_type t) | List.length l = n}
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
      let v := N2Bv_sized n x in exist _ (Vector.to_list v) (to_list_length v)
    | _ => fun f x => map f x
    end f
  | Pair x y => fun '(x,y) => (denote1_to_denote x, denote1_to_denote y)
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

Definition vector_head {t n}: denote_type (Vec t (S n)) -> denote_type t * denote_type (Vec t n) := hd_safe.

Fixpoint vector_as_tuple n t {struct n}: denote_type (Vec t (S n)) -> denote_type (ntuple t n) :=
  match n with
  | O => fun x => fst (vector_head x)
  | S n' => fun ls =>
    let '(hd,tl) := vector_head ls in
    (hd, vector_as_tuple n' _ tl)
  end.
Definition vector_as_tuple1 n t (x: denote1_type (Vec t (S n))): denote_type (ntuple t n) :=
  vector_as_tuple _ _ (denote1_to_denote x).

Section test.
  Import ListNotations.
  Compute (vector_as_tuple1 _ _ (exist _ [0;1;2] _:denote1_type (Vec (BitVec 3) 3)))%N.
  Compute (vector_as_tuple1 _ _ (exist _ [0;1;2] _:denote1_type (Vec (BitVec 3) 3)))%N.
End test.

Declare Scope circuit_type_scope.
Delimit Scope circuit_type_scope with circuit_type.
Open Scope circuit_type_scope.
Notation "[ ]" := unit (format "[ ]") : circuit_type_scope.
Notation "[ x ]" := (pair x unit) : circuit_type_scope.
Notation "[ x ; y ; .. ; z ]" := (pair x (pair y .. (pair z unit) ..)) : circuit_type_scope.
Notation "x ** y" := (pair x y)(at level 60, right associativity) : circuit_type_scope.
Notation "x ++ y" := (absorb_any x y) (at level 60, right associativity): circuit_type_scope.

