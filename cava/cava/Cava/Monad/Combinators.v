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

From Coq Require Import Lists.List Lia.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.MonadFix.
From Coq Require Arith.PeanoNat.
Require Import Omega.

Export MonadNotation.

From Cava Require Import Kind.
Require Import Cava.Monad.CavaClass.
Require Import Cava.VectorUtils.

Generalizable All Variables.

From Coq Require Import Lia.

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

Fixpoint treeWithList {T: Type} {m bit} `{Cava m bit}
                      (circuit: T -> T -> m T) (def: T)
                      (n : nat) (v: Vector.t T (2^(n+1))) : m T :=
 treeList circuit def n (to_list v).

(******************************************************************************)
(* A binary tree combinator, Vector version.                                                  *)
(******************************************************************************)

Definition resize {A n} m (Hlen : n = m) (v : t A n) : t A m.
  subst; apply v.
Defined.

Lemma pow2_succ_double n : 2 ^ (S n) = 2 ^ n + 2 ^ n.
Proof. rewrite Nat.pow_succ_r'; lia. Qed.

Definition divide {A n} (v : Vector.t A (2 ^ (S n))) :
    Vector.t A (2 ^ n) * Vector.t A (2 ^ n) :=
    splitat _ (@resize A (2 ^ (S n)) (2 ^ n + 2 ^ n) (pow2_succ_double n) v).

Fixpoint tree {T: Type} {m bit} `{Cava m bit} (n: nat)
                                (circuit: T -> T -> m T)
                                (v : Vector.t T (2^(S n))) :
                                m T :=
  match n, v return m T with
  | O, v2 => circuit (@Vector.nth_order _ 2 v2 0 (ltac:(lia)))
                     (@Vector.nth_order _ 2 v2 1 (ltac:(lia)))
  | S n', vR => let '(vL, vH) := divide vR in
                aS <- tree n' circuit vL ;;
                bS <- tree n' circuit vH ;;
                circuit aS bS
  end.

(* Lemmas about [resize] *)
Section resize.
  Lemma resize_prf_irr {A} n m Hlen1 Hlen2 (v : t A n) :
    resize m Hlen1 v = resize m Hlen2 v.
  Proof.
  subst. rewrite (Eqdep.EqdepTheory.UIP_refl _ _ Hlen2).
  reflexivity.
  Qed.

  Lemma resize_id {A} n H (v : t A n) : v = resize n H v.
  Proof. rewrite resize_prf_irr with (Hlen2:=eq_refl). reflexivity. Qed.

  Lemma resize_cons {A} n m Hlen a (v : t A n) :
    resize (S m) Hlen (a :: v)%vector = (a :: resize m (eq_add_S _ _ Hlen) v)%vector.
  Proof.
    intros. assert (n = m) by lia. subst.
    rewrite <-!resize_id. reflexivity.
  Qed.

  Lemma resize_resize {A} n m p Hlen1 Hlen2 (v : t A n) :
    resize p Hlen2 (resize m Hlen1 v) = resize p (eq_trans Hlen1 Hlen2) v.
  Proof. subst; reflexivity. Qed.

  Lemma fold_left_resize {A B} (f : B -> A -> B) n m H b (v : t A n) :
    Vector.fold_left f b (resize m H v) = Vector.fold_left f b v.
  Proof. subst. rewrite <-resize_id. reflexivity. Qed.
End resize.

(* Vector facts *)
Module Vector.
  Lemma tl_0 {A} (v : t A 1) : Vector.tl v = Vector.nil A.
  Proof.
    eapply case0 with (v:=Vector.tl v).
    reflexivity.
  Qed.

  Lemma hd_0 {A} (v : t A 1) : Vector.hd v = Vector.last v.
  Proof.
    rewrite (eta v).
    eapply case0 with (v:=Vector.tl v).
    reflexivity.
  Qed.

  Lemma last_tl {A} n (v : t A (S (S n))) :
    Vector.last (Vector.tl v) = Vector.last v.
  Proof. rewrite (eta v); reflexivity. Qed.

  Lemma fold_left_S {A B : Type} (f : B -> A -> B) b n (v : t A (S n)) :
      Vector.fold_left f b v = Vector.fold_left
                                 f (f b (Vector.hd v)) (Vector.tl v).
  Proof. rewrite (eta v). reflexivity. Qed.

  Lemma fold_left_0 {A B : Type} (f : B -> A -> B) b (v : t A 0) :
      Vector.fold_left f b v = b.
  Proof. eapply case0 with (v:=v). reflexivity. Qed.

  Hint Rewrite @Vector.fold_left_S @Vector.fold_left_0
       using solve [eauto] : push_vector_fold vsimpl.

  Lemma fold_left_append {A B} (f : A -> B -> A) :
    forall n m start (v1 : t B n) (v2 : t B m),
      Vector.fold_left f start (v1 ++ v2)%vector
      = Vector.fold_left f (Vector.fold_left f start v1) v2.
  Proof.
    induction n; intros;
      lazymatch goal with
      | v' : t _ 0 |- _ =>
        eapply case0 with (v:=v')
      | v : t _ (S _) |- _ => rewrite (eta v)
      end;
      [ reflexivity | ].
    rewrite <-append_comm_cons.
    cbn [Vector.fold_left].
    rewrite IHn. reflexivity.
  Qed.

  Lemma fold_left_S_identity {A} (f : A -> A -> A) id
        (left_identity : forall a, f id a = a) n (v : t A (S n)) :
    Vector.fold_left f id v = Vector.fold_left f (Vector.hd v) (Vector.tl v).
  Proof.
    intros. rewrite (eta v).
    rewrite !fold_left_S, left_identity.
    reflexivity.
  Qed.

  Lemma fold_left_S_assoc {A} (f : A -> A -> A) id
        (right_identity : forall a, f a id = a)
        (left_identity : forall a, f id a = a)
        (associative :
           forall a b c, f a (f b c) = f (f a b) c) :
    forall n start (v : t A n),
      Vector.fold_left f start v = f start (Vector.fold_left f id v).
  Proof.
    induction n; intros; autorewrite with push_vector_fold.
    { rewrite right_identity. reflexivity. }
    { rewrite left_identity.
      erewrite <-fold_left_S_identity by eauto.
      rewrite IHn, <-associative.
      rewrite fold_left_S with (b:=id).
      f_equal. rewrite !left_identity, <-IHn.
      reflexivity. }
  Qed.
End Vector.
Hint Rewrite @Vector.fold_left_S @Vector.fold_left_0
     using solve [eauto] : push_vector_fold vsimpl.
Hint Rewrite @Vector.tl_0 @Vector.hd_0 @Vector.last_tl
     using solve [eauto] : push_vector_tl_hd_last vsimpl.
Hint Rewrite @Vector.nth_order_hd @Vector.nth_order_last
     using solve [eauto] : push_vector_nth_order vsimpl.

Local Ltac destruct_pair_let :=
  match goal with
  | |- context [ match ?p with pair _ _ => _ end ] =>
    rewrite (surjective_pairing p)
  end.

Require Import ExtLib.Structures.MonadLaws.

Lemma append_divide {A} n H (v : t A (2 ^ (S n))) :
  (fst (divide v) ++ snd (divide v))%vector = resize _ H v.
Proof.
  cbv [divide].
  let H := fresh in
  match goal with
  | |- context [splitat ?n ?v] =>
    pose proof (surjective_pairing (splitat n v)) as H
  end;
    apply append_splitat in H;
    rewrite <-H; clear H.
  apply resize_prf_irr.
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
      (n : nat) :
  forall v,
    tree n circuit v = ret (Vector.fold_left op id v).
Proof.
  induction n; intros.
  { change (2 ^ 1) with 2 in *.
    cbn [tree]. autorewrite with vsimpl.
    rewrite circuit_equiv, op_id_left. reflexivity. }
  { cbn [tree]. destruct_pair_let.
    rewrite !IHn, !bind_of_return, circuit_equiv by typeclasses eauto.
    rewrite <-Vector.fold_left_S_assoc, <-Vector.fold_left_append by auto.
    rewrite append_divide with (H:=pow2_succ_double _).
    rewrite fold_left_resize. reflexivity. }
Qed.
