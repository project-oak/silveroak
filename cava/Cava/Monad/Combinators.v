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

Require Import Coq.Vectors.Vector.
Import VectorNotations.

Require Import Coq.Lists.List Coq.micromega.Lia.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Require Import Coq.Arith.PeanoNat.

Export MonadNotation.

Require Import Cava.Monad.CavaClass.
Require Import Cava.VectorUtils.
Require Import Cava.ListUtils.
Require Import Cava.Signal.
Require Import Cava.Tactics.

Generalizable All Variables.

Require Import ExtLib.Structures.MonadLaws.

Local Open Scope monad_scope.
Local Open Scope type_scope.

Section WithCava.
  Context {signal} `{m: Cava signal}.
  Context {monad: Monad cava}.

  (****************************************************************************)
  (* Lava-style circuit combinators.                                          *)
  (****************************************************************************)

  (* Use a circuit to zip together two vectors. *)
  Definition zipWith {A B C : SignalType} {n : nat}
           (f : signal A * signal B -> cava (signal C))
           (a : signal (Vec A n))
           (b : signal (Vec B n))
           : cava (signal (Vec C n)) :=
    let a' := peel a in
    let b' := peel b in
    v <- mapT f (vcombine a' b') ;;
    ret (unpeel v).

  (* A list-based left monadic-fold. *)
  Fixpoint foldLM {m} `{Monad m} {A B : Type}
                  (f : B -> A -> m B)
                  (input : list A) 
                  (accum : B) 
                  : m B :=
    match input with
    | [] => ret accum
    | k::ks => st' <- f accum k  ;;
               foldLM f ks st'
    end.

  Lemma foldLM_fold_right {A B}
        (bind_ext : forall {A B} x (f g : A -> cava B),
            (forall y, f y = g y) -> bind x f = bind x g)
        (f : B -> A -> cava B) (input : list A) (accum : B) :
    foldLM f input accum =
    List.fold_right
      (fun k continuation v => bind (f v k) continuation)
      ret input accum.
  Proof.
    revert accum; induction input; intros; [ reflexivity | ].
    cbn [foldLM List.fold_right].
    eapply bind_ext; intros.
    rewrite IHinput. reflexivity.
  Qed.

  Lemma foldLM_ident_fold_left
        {A B} (f : B -> A -> ident B) ls b :
    unIdent (foldLM f ls b) = List.fold_left (fun b a => unIdent (f b a)) ls b.
  Proof.
    revert b; induction ls; [ reflexivity | ].
    cbn [foldLM List.fold_left]. intros.
    cbn [bind ret Monad_ident].
    rewrite IHls. reflexivity.
  Qed.

  (* Below combinator

  -----------------------------------------------------------------------------
  -- Below
  -----------------------------------------------------------------------------
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
  -----------------------------------------------------------------------------
  *)

  Definition below {A B C D E F G}
              (r : A * B -> cava (D * G))
              (s : G * C -> cava (E * F))
              (abc : A * (B * C)) : cava ((D * E) * F) :=
    let (a, bc) := abc in
    let (b, c) := bc in
    dg <- r (a, b) ;;
    let (d, g) := dg : D * G in
    ef <- s (g, c) ;;
    let (e, f) := ef : E * F in
    ret ((d, e), f).

  (* The col combinator takes a 4-sided circuit element and replicates it by
    composing each element in a chain.

  -----------------------------------------------------------------------------
  -- 4-Sided Tile Combinators
  -----------------------------------------------------------------------------
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
  -----------------------------------------------------------------------------

  *)

  (* colV is a col combinator that works over Vector.t of signals.
    The input tuple is split into separate arguments so Coq can recognize
    the decreasing vector element.
  *)

  Local Open Scope vector_scope.

  Fixpoint colV' {A B C} {n : nat}
                (circuit : A * B -> cava (C * A))
                (aIn: A) (bIn: Vector.t B n) :
                cava (Vector.t C n * A) :=
    match bIn with
    | [] => ret ([], aIn)
    | x::xs => '(b0, aOut) <- circuit (aIn, x) ;;
               '(bRest, aFinal) <- colV' circuit aOut xs ;;
                ret (b0::bRest, aFinal)
    end.

  Definition colV {A B C} {n : nat}
                  (circuit : A * B -> cava (C * A))
                  (inputs: A * Vector.t B n) :
                  cava (Vector.t C n * A) :=
  colV' circuit (fst inputs) (snd inputs).

  (****************************************************************************)
  (* Make the Cava signal-level col combinator use the vector-based colV      *)
  (* under the hood.                                                          *)
  (****************************************************************************)

  Definition col {A B C} {n : nat}
               (circuit : signal A * signal B -> cava (signal C * signal A))
               (aIn: signal A) (bIn: signal (Vec B n)) :
               cava (signal (Vec C n) * signal A) :=
  '(c, a) <- colV circuit (aIn, (peel bIn)) ;;
  ret (unpeel c, a).

  Local Close Scope vector_scope.

  (* List Variant *)

  Local Open Scope list_scope.

  Fixpoint colL' {m} `{Monad m} {A B C}
                (circuit : A * B -> m (C * A))
                (aIn: A) (bIn: list B) :
                m (list C * A) :=
    match bIn with
    | [] => ret ([], aIn)
    | x::xs => '(b0, aOut) <- circuit (aIn, x) ;;
              '(bRest, aFinal) <- colL' circuit aOut xs ;;
                ret (b0::bRest, aFinal)
    end.

  Definition colL {m} `{Monad m} {A B C}
                  (circuit : A * B -> m (C * A))
                  (inputs: A * list B) :
                  m (list C * A) :=
  colL' circuit (fst inputs) (snd inputs).

  Local Close Scope vector_scope.

  (****************************************************************************)
  (* Forks in wires                                                           *)
  (****************************************************************************)

  Definition fork2 `{Mondad_m : Monad cava} {A} (a:A) := ret (a, a).

  Definition first `{Mondad_m : Monad cava} {A B C} (f : A -> cava C) (ab : A * B) : cava (C * B) :=
    let '(a, b) := ab in
    c <- f a ;;
    ret (c, b).

  Definition second `{Mondad_m : Monad cava} {A B C} (f : B -> cava C) (ab : A * B) : cava (A * C) :=
    let '(a, b) := ab in
    c <- f b ;;
    ret (a, c).

  (****************************************************************************)
  (* Split a bus into two halves.                                             *)
  (****************************************************************************)

  Definition halve {A} (l : list A) : list A * list A :=
    let mid := (length l) / 2 in
    (firstn mid l, skipn mid l).

  (****************************************************************************)
  (* A binary tree combinator, list version.                                                *)
  (****************************************************************************)

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

  Definition treeWithList {T: Type} {m} `{Monad m}
                          (circuit: T -> T -> m T) (def: T)
                          (n : nat) (v: Vector.t T (2^(n+1))) : m T :=
    treeList circuit def n (to_list v).

  Lemma treeList_equiv
        {T} {cava} {monad' : Monad cava}
        {monad_laws : MonadLaws monad'}
        (id : T)
        (op : T -> T -> T)
        (op_id_left : forall a : T, op id a = a)
        (op_id_right : forall a : T, op a id = a)
        (op_assoc :
          forall a b c : T,
            op a (op b c) = op (op a b) c)
        (circuit : T -> T -> cava T)
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

  (****************************************************************************)
  (* A binary tree combinator, Vector version.                                                  *)
  (****************************************************************************)

  Definition divide {A n} (default : A) (v : Vector.t A (2 ^ (S n))) :
    Vector.t A (2 ^ n) * Vector.t A (2 ^ n) :=
    splitat _ (@resize_default A (2 ^ (S n)) default (2 ^ n + 2 ^ n) v).

  Fixpoint treeS {t: SignalType}
                          {n : nat}
                          (circuit: signal t -> signal t -> cava (signal t))
                          (v : Vector.t (signal t) (2^(S n))) :
                          cava (signal t) :=
    match n, v return cava (signal t) with
    | O, v2 => circuit (@Vector.nth_order _ 2 v2 0 (ltac:(lia)))
                       (@Vector.nth_order _ 2 v2 1 (ltac:(lia)))
    | S n', vR => let '(vL, vH) := divide defaultSignal vR in
                  aS <- treeS circuit vL ;;
                  bS <- treeS circuit vH ;;
                  circuit aS bS
    end.

  Fixpoint tree {T: Type} {m} `{Monad m}
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

  Local Open Scope nat_scope.

  Lemma tree_equiv
        {T}  {monad_laws : MonadLaws monad}
        (id : T)
        (op : T -> T -> T)
        (op_id_left : forall a : T, op id a = a)
        (op_id_right : forall a : T, op a id = a)
        (op_assoc :
          forall a b c : T,
            op a (op b c) = op (op a b) c)
        (circuit : T -> T -> cava T)
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

 End WithCava.