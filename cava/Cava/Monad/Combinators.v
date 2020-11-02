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

From Coq Require Import Vectors.Vector.
Import VectorNotations.

From Coq Require Import Lists.List micromega.Lia.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.MonadFix.
From Coq Require Import Arith.PeanoNat.

Export MonadNotation.

From Cava Require Import Kind.
Require Import Cava.Monad.CavaClass.
Require Import Cava.VectorUtils.
Require Import Cava.ListUtils.
Require Import Cava.Tactics.

Generalizable All Variables.

Require Import ExtLib.Structures.MonadLaws.

Local Open Scope monad_scope.


(******************************************************************************)
(* Lava-style circuit combinators.                                            *)
(******************************************************************************)

(* Below combinator

-------------------------------------------------------------------------------
-- Below
-------------------------------------------------------------------------------
-- below r s
--            ^
--            |
--            f
--            ^
--            |
--          -----
--         |     |
--     c ->|  s  |-> e
--         |     |
--          -----
--            ^
--            |
--            g
--            ^
--            |
--          -----
--         |     |
--     b ->|  r  |-> d
--         |     |
--          -----
--            ^
--            |
--            a
-------------------------------------------------------------------------------
*)

Fixpoint below `{Monad m} {A B C D E F G}
             (r : A * B -> m (D * G)%type)
             (s : G * C -> m (E * F)%type)
             (abc : A * (B * C)) : m ((D * E) * F)%type :=
  let (a, bc) := abc in
  let (b, c) := bc in
  dg <- r (a, b) ;;
  let (d, g) := dg : D * G in
  ef <- s (g, c) ;;
  let (e, f) := ef : E * F in
  ret ((d, e), f).

(* The col combinator takes a 4-sided circuit element and replicates it by
   composing each element in a chain.

-------------------------------------------------------------------------------
-- 4-Sided Tile Combinators
-------------------------------------------------------------------------------
-- COL r
--            a
--            ^
--            |
--          -----
--         |     |
--     b ->|  r  |-> c
--         |     |
--          -----
--            ^
--            |
--            a
--            ^
--            |
--          -----
--         |     |
--     b ->|  r  |-> c
--         |     |
--          -----
--            ^
--            |
--            a
--            ^
--            |
--          -----
--         |     |
--     b ->|  r  |-> c
--         |     |
--          -----
--            ^
--            |
--            a
-------------------------------------------------------------------------------


*)

(* The below_cons' is a convenient combinator for composing
   homogenous tiles that are expressed with curried inputs.
*)
Definition below_cons' `{Monad m} {A B C}
             (r : C -> A -> m (B * C)%type)
             (s : C -> list A -> m (list B * C)%type)
             (c: C) (a : list A) : m (list B * C)%type :=
  match a with
  | [] => ret ([], c)
  | a0::ax => '(b0, c1) <- r c a0  ;;
              '(bx, cOut) <- s c1 ax ;;
              ret (b0::bx, cOut)
  end.

(* col' is a curried version of col which ca be defined
   recursively because Coq can figure out the decreasing
   argument i.e. a
*)
Fixpoint col' `{Monad m} {A B C}
              (circuit : C -> A -> m (B * C)%type) (c: C) (a: list A) :
              m (list B * C)%type :=
  below_cons' circuit (col' circuit) c a.

(* A useful fact about how a col' of a circuit can be made using one
   instance of a circuit below a col' that is one smaller.
*)
Lemma col_cons': forall `{Monad m} {A B C} (r : C -> A -> m (B * C)%type) (c: C) (a: list A),
                col' r c a = below_cons' r (col' r) c a.
Proof.
  intros.
  destruct a.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* To define the pair to pair tile variants of col and below_cons
   it is useful to have some functions for currying and uncurrying,
   with we borrow from Logical Foundations. *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z
  := f (fst p) (snd p).

(* Thank you Benjamin. *)

(* Now we can define the col combinator that works with tiles that
   map pairs to pairs by using col'.
*)
Definition col `{Monad m} {A B C}
              (circuit : C * A -> m (B * C)%type) :
              C * list A -> m (list B * C)%type :=
  prod_uncurry (col' (prod_curry circuit)).

(* Define a version of below_cons' that works on pair to pair tiles *)

Definition below_cons `{Monad m} {A B C}
             (r : C * A -> m (B * C)%type)
             (s : C * list A -> m (list B * C)%type) :
             C * list A -> m (list B * C)%type :=
  prod_uncurry (below_cons' (prod_curry r) (prod_curry s)).

(* A useful fact about how a col of a circuit can be made using one
   instance of a circuit below a col that is one smaller.
*)
Lemma col_cons: forall `{Monad m} {A B C} (r : C * A -> m (B * C)%type)
                (ca: C * list A),
                col r ca = below_cons r (col r) ca.
Proof.
  intros.
  destruct ca.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Import EqNotations.

Local Open Scope vector_scope.

Lemma add_S_contra: forall x y, x = S y -> x - 1 <> y -> False.
Proof. lia. Qed.

Lemma S_add_S_contra: forall x y, x = S y -> S (x - 1) <> S y -> False.
Proof. lia. Qed.

Definition vec_dec_rewrite1 {A x y} (H: x = S y) (v: Vector.t A y): Vector.t A (x - 1) :=
  match Nat.eq_dec (x - 1) y with
  | left Heq => rew <- Heq in v
  | right Hneq => match add_S_contra _ _ H Hneq with end
  end.

Definition vec_dec_rewrite2 {A x y} (H: x = S y) (v: Vector.t A (S (x - 1))): Vector.t A (S y) :=
  match Nat.eq_dec (S (x - 1)) (S y) with
  | left Heq => rew Heq in v
  | right Hneq => match S_add_S_contra _ _ H Hneq with end
  end.

Program Definition below_consV `{Monad m} {A B C} {n: nat}
              (r : C -> A -> m (B * C)%type)
              (s : C -> Vector.t A (n-1) -> m (Vector.t B (n-1) * C)%type)
              (ca: C * Vector.t A n) : m (Vector.t B n * C)%type :=
  let '(c, a) := ca in
  match a in Vector.t _ z return n=z -> m (Vector.t B z * C)%type with
  | Vector.nil _ => fun _ => ret ([], c)
  | Vector.cons _ a0 Z ax => fun H =>
    '(b0, c1) <- r c a0 ;;
    '(bx, cOut) <- s c1 (vec_dec_rewrite1 H ax) ;;
    ret (vec_dec_rewrite2 H (b0 :: bx), cOut)
  end eq_refl.

Definition circuit_dec_rewrite `{Monad m} {A B C x y} (H: x = S y)
  (s: C -> Vector.t A y -> m (Vector.t B y * C)%type)
  : C -> Vector.t A (x-1) -> m (Vector.t B (x-1) * C)%type :=
  match Nat.eq_dec (x - 1) y with
  | left Heq => rew <- [fun z => C -> Vector.t A z -> m (Vector.t B z * C)%type] Heq in s
  | right Hneq => match add_S_contra _ _ H Hneq with end
  end.

Fixpoint colV `{Monad m} {A B C} (n: nat)
              (circuit : C -> A -> m (B * C)%type)
              (c: C) (a: Vector.t A n) :
              m (Vector.t B n * C)%type :=
  match n as n' return n=n' -> m (Vector.t B n' * C)%type with
  | O => fun _ => ret ([], c)
  | S n0 => fun H =>
    let s :=  circuit_dec_rewrite H (colV n0 circuit) in
    '(x,c) <- below_consV circuit s (c, a) ;;
    ret (rew H in x, c)
  end eq_refl.

Local Close Scope vector_scope.

(******************************************************************************)
(* Forks in wires                                                             *)
(******************************************************************************)

Definition fork2 `{Mondad_m : Monad m} {A} (a:A) := ret (a, a).

Definition first `{Mondad_m : Monad m} {A B C} (f : A -> m C) (ab : A * B) : m (C * B)%type :=
  let '(a, b) := ab in
  c <- f a ;;
  ret (c, b).

Definition second `{Mondad_m : Monad m} {A B C} (f : B -> m C) (ab : A * B) : m (A * C)%type :=
  let '(a, b) := ab in
  c <- f b ;;
  ret (a, c).

(******************************************************************************)
(* Split a bus into two halves.                                               *)
(******************************************************************************)

Definition halve {A} (l : list A) : list A * list A :=
  let mid := (length l) / 2 in
  (firstn mid l, skipn mid l).

(******************************************************************************)
(* A binary tree combinator, list version.                                                  *)
(******************************************************************************)

Fixpoint treeList {T: Type} {m} `{Monad m}
                  (circuit: T -> T -> m T) (def: T)
                  (n : nat) (v: list T) : m T :=
  match n with
  | O => match v return m T with
        | [a; b]=> circuit a b
        | _ => ret def
        end
  | S n' => let '(vL, vH) := halve v in
           aS <- treeList circuit def n' vL ;;
           bS <- treeList circuit def n' vH ;;
           circuit aS bS
  end.

Fixpoint treeWithList {T: Type} {m bit} `{Cava m bit}
                      (circuit: T -> T -> m T) (def: T)
                      (n : nat) (v: Vector.t T (2^(n+1))) : m T :=
  treeList circuit def n (to_list v).

Lemma treeList_equiv
      {T} {m} {monad : Monad m}
      {monad_laws : MonadLaws monad}
      (id : T)
      (op : T -> T -> T)
      (op_id_left : forall a : T, op id a = a)
      (op_id_right : forall a : T, op a id = a)
      (op_assoc :
         forall a b c : T,
           op a (op b c) = op (op a b) c)
      (circuit : T -> T -> m T)
      (circuit_equiv :
         forall a b : T, circuit a b = ret (op a b))
      (def : T) (n : nat) :
  forall v,
    length v = 2 ^ (S n) ->
    treeList circuit def n v = ret (List.fold_left op v id).
Proof.
  induction n; intros; [ | ].
  { (* n = 0 *)
    change (2 ^ 1) with 2 in *.
    destruct_lists_by_length. cbn [treeList fold_left].
    rewrite op_id_left, circuit_equiv.
    reflexivity. }
  { (* n = S n' *)
    cbn [treeList halve]. rewrite !Nat.pow_succ_r in * by lia.
    erewrite <-Nat.div_unique_exact by eauto.
    rewrite !IHn by (rewrite ?firstn_length, ?skipn_length; lia).
    rewrite !bind_of_return, circuit_equiv by typeclasses eauto.
    rewrite <-fold_left_assoc, <-fold_left_app by eauto.
    rewrite firstn_skipn. reflexivity. }
Qed.

(******************************************************************************)
(* A binary tree combinator, Vector version.                                                  *)
(******************************************************************************)

Definition divide {A n} (default : A) (v : Vector.t A (2 ^ (S n))) :
  Vector.t A (2 ^ n) * Vector.t A (2 ^ n) :=
  splitat _ (@resize_default A (2 ^ (S n)) default (2 ^ n + 2 ^ n) v).

Fixpoint tree {T: Type} {m bit} `{Cava m bit}
                                (default : T) (n : nat)
                                (circuit: T -> T -> m T)
                                (v : Vector.t T (2^(S n))) :
                                m T :=
  match n, v return m T with
  | O, v2 => circuit (@Vector.nth_order _ 2 v2 0 (ltac:(lia)))
                     (@Vector.nth_order _ 2 v2 1 (ltac:(lia)))
  | S n', vR => let '(vL, vH) := divide default vR in
                aS <- tree default n' circuit vL ;;
                bS <- tree default n' circuit vH ;;
                circuit aS bS
  end.

Lemma append_divide {A} d n H (v : t A (2 ^ (S n))) :
  (fst (divide d v) ++ snd (divide d v))%vector = resize _ H v.
Proof.
  cbv [divide].
  let H := fresh in
  match goal with
  | |- context [splitat ?n ?v] =>
    pose proof (surjective_pairing (splitat n v)) as H
  end;
    apply append_splitat in H;
    rewrite <-H; clear H.
  rewrite resize_default_eq with (d0:=d).
  reflexivity.
Qed.

Lemma tree_equiv
      {T} {m bit} {monad : Monad m}
      {cava : Cava m bit} {monad_laws : MonadLaws monad}
      (id : T)
      (op : T -> T -> T)
      (op_id_left : forall a : T, op id a = a)
      (op_id_right : forall a : T, op a id = a)
      (op_assoc :
         forall a b c : T,
           op a (op b c) = op (op a b) c)
      (circuit : T -> T -> m T)
      (circuit_equiv :
         forall a b : T, circuit a b = ret (op a b))
      (default : T) (n : nat) :
  forall v,
    tree default n circuit v = ret (Vector.fold_left op id v).
Proof.
  induction n; intros.
  { change (2 ^ 1) with 2 in *.
    cbn [tree]. autorewrite with push_vector_fold vsimpl.
    rewrite circuit_equiv, op_id_left. reflexivity. }
  { cbn [tree]. destruct_pair_let.
    rewrite !IHn by eauto.
    rewrite !bind_of_return by eauto.
    rewrite circuit_equiv by eauto.
    rewrite <-fold_left_S_assoc, <-fold_left_append by auto.
    assert (2 ^ S (S n) = 2 ^ S n + 2 ^ S n)
      by (rewrite Nat.pow_succ_r'; lia).
    rewrite (append_divide _ _ ltac:(eassumption)).
    rewrite fold_left_resize. reflexivity. }
Qed.
