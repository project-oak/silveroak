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

Require Import Vector.
Import VectorNotations.

From Coq Require Import Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.MonadFix.
From Coq Require Arith.PeanoNat.
Require Import Omega.

Export MonadNotation.

From Cava Require Import Kind.
Require Import Cava.Monad.CavaClass.

Generalizable All Variables.

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

Definition below_consV `{Monad m} {A B C} {n: nat}
              (r : C -> A -> m (B * C)%type)
              (s : C -> Vector.t A n -> m (Vector.t B n * C)%type)
              (ca: C * Vector.t A (S n)) : m (Vector.t B (S n) * C)%type :=
  let '(c, a) := ca in
  match a in Vector.t _ z return (S n)=z -> m (Vector.t B z * C)%type with
  | Vector.nil _ => fun H => match Nat.neq_succ_0 n H with end
  | Vector.cons _ a0 Z ax => 
              fun H => 
              (
              '(b0, c1) <- r c a0 ;;
              '(bx, cOut) <- s c1 (rew <- [Vector.t A] (eq_add_S _ _ H) in ax) ;;
              ret (rew [Vector.t B] H in (b0 :: bx), cOut)
              )
  end eq_refl.

Fixpoint colV `{Monad m} {A B C} (n: nat)
              (circuit : C -> A -> m (B * C)%type) 
              (c: C) (a: Vector.t A (S n)) :
              m (Vector.t B (S n) * C)%type :=
  match n as n' return n=n' -> m (Vector.t B (S n') * C)%type with
  | O => fun _ =>
    '(b, c) <- circuit c (@nth_order _ _ a 0 (Nat.lt_0_succ _)) ;;
    ret ([b], c)
  | S n0 => fun H => 
    let x := below_consV circuit (
      rew <- [fun z => C -> Vector.t A (z) -> m (Vector.t B (z)* C)%type] H in 
      colV n0 circuit) (c, a) in
    rew [fun z => m (Vector.t B (S z) * C)%type] H in x
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

Fixpoint treeList {T: Type} {m bit} `{Cava m bit}
                  (circuit: T -> T -> m T) (def: T) 
                  (n : nat) (v: list T) : m T :=
  match n, v with
  | O, ab => match ab return m T with
             | [a; b]=> circuit a b
             | _ => ret def
             end
  | S n', vR => let '(vL, vH) := halve v in
                aS <- treeList circuit def n' vL ;;
                bS <- treeList circuit def n' vH ;;
                circuit aS bS
  end.

Fixpoint tree {T: Type} {m bit} `{Cava m bit}
              (circuit: T -> T -> m T) (def: T) 
              (n : nat) (v: Vector.t T (2^(n+1))) : m T :=
 treeList circuit def n (to_list v).

(******************************************************************************)
(* A binary tree combinator, Vector version.                                                  *)
(******************************************************************************)

Program Definition halveV {n a} (v : Vector.t a (2*n)) : Vector.t a n * Vector.t a n :=
  splitat n v.

Local Open Scope vector_scope.

Fixpoint treeV {T: Type} {m bit} `{Cava m bit} (n: nat)
                                 (circuit: T -> T -> m T)
                                 (v : Vector.t T (2^(n+1))) :
                                 m T :=
  match n, v return m T with
  | O, v2 => circuit (Vector.hd v2) (Vector.hd (Vector.tl v2))
  | S n', vR => let '(vL, vH) := halveV vR in
                aS <- treeV n' circuit vL ;;
                bS <- treeV n' circuit vH ;;
                circuit aS bS
  end.

Local Close Scope vector_scope.  