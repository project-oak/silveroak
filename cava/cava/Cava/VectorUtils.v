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

From Coq Require Import Lists.List.
Import ListNotations.

From Coq Require Import Vector.
Import VectorNotations.

From Coq Require Import ZArith.
Require Import Nat Arith Lia.

From ExtLib Require Import Structures.Applicative.
From ExtLib Require Import Structures.Traversable.
Require Export ExtLib.Data.Monads.IdentityMonad.

Section traversable.
  Universe u v vF.
  Context {F : Type@{v} -> Type@{vF}}.
  Context {Applicative_F : Applicative F}.
  Context {A : Type@{u}} {B : Type@{v}}.
  Variable f : A -> F B.

  Fixpoint mapT_vector@{} {n} (v : Vector.t A n ) : F (Vector.t B n).
  Proof.
    inversion v.
    exact (@pure F _ _ []%vector).
    refine (
        let _1 := fun y ys => @Vector.cons B y _ ys in
        let _2 := @pure F _ _ _1 in
        let _3 := @ap F _ _ _ _2 (f h) in
        let xs' := mapT_vector _ X in
        let _4 := @ap F _ _ _  _3 in
        _
    ).
    apply _4 in xs' .
    exact xs'.
  Defined.
End traversable.

Definition fixup n (F : Type -> Type) (Ap: Applicative F) (A B : Type) (m: A -> F B) := @mapT_vector F Ap A B m n.

Global Instance Traversable_vector@{} {n} : Traversable (fun t => Vector.t t n) :=
{ mapT := fixup n }.

Local Open Scope vector_scope.

Section Vector.
  Context {A:Type}.
  Local Notation t := (Vector.t).

  Fixpoint vreshape {n m}: t A (n * m) -> t (t A m) n :=
    match n as n' return t A (n' * m) -> t (t A m) n' with
    | 0 => fun _ => []
    | S n' => fun v =>
      let '(x, xs) := Vector.splitat (r:=n' * m) m v in
      x :: vreshape xs
    end.

  Fixpoint vflatten {n m}: t (t A m) n -> t A (n*m) :=
    match n as n' return t (t A m) n' -> t A (n'*m) with
    | 0 => fun _ => []
    | S n' => fun v =>
        let '(x, xs) := uncons v in
        x ++ vflatten xs
    end.

  Definition vunsnoc {n} (v: t A (S n)): (t A n * A) :=
    rectS (fun n v => (t A n * A)%type)
    (fun o => ([], o))
    (fun o n v f =>
      let '(xs, x) := f in
      (o::xs, x)
    ) v.

  Definition vsnoc {n} (v: t A n) a: t A (S n) :=
    t_rect _ (fun n v => t A (S n)) [a]
    (fun x n v f =>
      x :: f
    ) _ v.

  (* avoids the equality rewrites in Coq.Vector.rev *)
  Fixpoint vreverse {n} (v: t A n): t A n :=
    match v with
    | [] => []
    | x::xs => vsnoc (vreverse xs) x
    end.
End Vector.

(******************************************************************************)
(* Vector version of combine                                                  *)
(******************************************************************************)

Fixpoint vcombine {A B: Type} {s: nat} (a: Vector.t A s)
                                       (b: Vector.t B s) :
                                       Vector.t (A * B) s :=

  match s, a, b with
  | O, _, _ => []
  | S n, a, b => let (x, xs) := Vector.uncons a in
                 let (y, ys) := Vector.uncons b in
                 (x, y) :: vcombine xs ys
  end.

Local Close Scope vector_scope.

(* Vector version of seq *)

Program Definition vseq (start len: nat) : Vector.t nat len :=
  Vector.of_list (List.seq start len).
Next Obligation.
  rewrite List.seq_length. reflexivity.
Defined.

(******************************************************************************)
(* Slicing a Vector.t                                                         *)
(******************************************************************************)

Import EqNotations.

Definition sliceVector {T: Type} {s: nat} (v: Vector.t T s) (startAt len : nat)
                     (H: startAt + len <= s) : Vector.t T len :=
  match Nat.eq_dec s (startAt + (s - startAt)) with
    | left Heq =>
      let '(_, v) := Vector.splitat startAt (rew [fun x => Vector.t T x] Heq in v)
      in
        match Nat.eq_dec (s-startAt) (len + ((s-startAt) - len)) with
        | left Heq => fst (Vector.splitat len (rew [fun x => Vector.t T x] Heq in v))
        | right Hneq => (ltac:(abstract lia))
        end
    | right Hneq => (ltac:(abstract lia))
    end.

(* An experimental alternative vector representation *)

Fixpoint AltVector (A: Type) (n: nat) : Type :=
  match n with
  | 0 => unit
  | S m => (A * AltVector A m)%type
  end.

Definition v1 : AltVector nat 3 := (1, (2, (3, tt))).

Fixpoint altVectorToList {A: Type} {n: nat} (v: AltVector A n) : list A :=
  match n, v with
  | 0, _ => []%list
  | _, (x, v) => x :: altVectorToList v
  end.

Lemma vecConsFactL: forall (A: Type) (n: nat),
      (A * AltVector A n)%type = AltVector A (n+1).
Proof.
  induction n.
  - auto.
  - simpl. rewrite IHn. reflexivity.
Qed.

Definition vecConsFact {A: Type} {n: nat} (v: A * AltVector A n) :
                                              AltVector A (n+1).
Proof.
  induction n.
  - auto.
  - simpl. rewrite Nat.add_1_r. apply v.
Qed.

Program Definition consAltVector {A: Type} {n: nat} (a: A) (v: AltVector A n) :
                         AltVector A (n+1) :=
   vecConsFact (a, v).

Lemma length_cons: forall A (x:A) (xs: list A), length (x :: xs) = length xs + 1.
Proof.
  induction xs.
  - simpl. reflexivity.
  - simpl. rewrite <- IHxs. simpl. reflexivity.
Qed.

Definition vec_cons {A} {x: A} {xs: list A} (v: AltVector A (length xs + 1)) :
                    AltVector A (length (x :: xs)).
Proof.
  rewrite length_cons.
  apply v.
Qed.

Fixpoint listToAltVector {A: Type} (l: list A) : AltVector A (length l) :=
  match l return AltVector A (length l)  with
  | [] => tt
  | x::xs => vec_cons (consAltVector x (listToAltVector xs))
  end.

Section resize.
  Context {A:Type}.
  Local Notation t := (Vector.t). (* for more concise type declarations *)

  Definition resize {n} m (Hlen : n = m) (v : t A n) : t A m.
    subst; apply v.
  Defined.

  Fixpoint resize_default {n} default : forall m, t A n -> t A m :=
    match n as n0 return forall m, t A n0 -> t A m with
    | O => fun m _ => Vector.const default m
    | S n' =>
      fun m v =>
        match m with
        | O => Vector.nil _
        | S m' => (Vector.hd v :: resize_default default m' (Vector.tl v))%vector
        end
    end.

  Lemma resize_default_id n d (v : t A n) :
    resize_default d n v = v.
  Proof.
    induction n; intros;
      [ eapply case0 with (v:=v); reflexivity | ].
    cbn [resize_default]. rewrite IHn.
    rewrite <-eta; reflexivity.
  Qed.

  Lemma resize_default_eq n m d H (v : t A n) :
    resize m H v = resize_default d m v.
  Proof.
    subst. rewrite resize_default_id. reflexivity.
  Qed.

  Lemma resize_prf_irr n m Hlen1 Hlen2 (v : t A n) :
    resize m Hlen1 v = resize m Hlen2 v.
  Proof.
    subst. rewrite (Eqdep_dec.UIP_refl_nat _ Hlen2).
    reflexivity.
  Qed.

  Lemma resize_id n H (v : t A n) : v = resize n H v.
  Proof. rewrite resize_prf_irr with (Hlen2:=eq_refl). reflexivity. Qed.

  Lemma resize_cons n m Hlen a (v : t A n) :
    resize (S m) Hlen (a :: v)%vector = (a :: resize m (eq_add_S _ _ Hlen) v)%vector.
  Proof.
    intros. assert (n = m) by lia. subst.
    rewrite <-!resize_id. reflexivity.
  Qed.

  Lemma resize_resize n m p Hlen1 Hlen2 (v : t A n) :
    resize p Hlen2 (resize m Hlen1 v) = resize p (eq_trans Hlen1 Hlen2) v.
  Proof. subst; reflexivity. Qed.

  Lemma fold_left_resize {B} (f : B -> A -> B) n m H b (v : t A n) :
    Vector.fold_left f b (resize m H v) = Vector.fold_left f b v.
  Proof. subst. rewrite <-resize_id. reflexivity. Qed.
End resize.

(* Miscellaneous facts about vectors *)
Section VectorFacts.
  Local Notation t := Vector.t.

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

  Hint Rewrite @fold_left_S @fold_left_0
       using solve [eauto] : push_vector_fold vsimpl.

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
End VectorFacts.
(* These hints create and populate the following autorewrite databases:
 * - push_vector_fold : simplify using properties of Vector.fold_left
 * - push_vector_tl_hd_last : simplify using properties of Vector.tl, Vector.hd,
     and Vector.last
 * - push_vector_nth_order : simplify expressions containing Vector.nth_order
 * - vsimpl : generic vector simplification, includes all of the above
 *
 * No hint added to one of these databases should leave any subgoals unsolved.
 *)
Hint Rewrite @fold_left_S @fold_left_0
     using solve [eauto] : push_vector_fold vsimpl.
Hint Rewrite @tl_0 @hd_0 @last_tl
     using solve [eauto] : push_vector_tl_hd_last vsimpl.
Hint Rewrite @nth_order_hd @nth_order_last
     using solve [eauto] : push_vector_nth_order vsimpl.

Section Vector.
  Context {A:Type}.
  Local Notation t := (Vector.t).
  Local Open Scope vector_scope.

  Definition slice_by_position n x y (default: A) (v: t A n): (t A (x - y + 1)) :=
    let v' := resize_default default (y + (n - y)) v in
    let tail := snd (splitat y v') in
    let tail' := resize_default default ((x - y + 1) + (n - x - 1)) tail in
    fst (splitat (x-y+1) tail').

  Definition separate {n B} (v: t (A*B) n): t A n * t B n :=
    t_rect _ (fun n v => t A n * t B n)%type ([],[])
    (fun '(x,y) n v f =>
      let '(xs,ys) := f in
      (x::xs,y::ys)
    ) _ v.

  Definition tail_default {n} (default: A) (v: t A n): t A (n-1) :=
    t_rect _ (fun n v => t A (n-1)) ([])
    (fun x n v f =>
      resize_default default _ v
    ) _ v.

  Fixpoint nth_default {n} (default: A) p (v: t A n): A :=
    match p with
    | 0 =>
        match v with
        | [] => default
        | x :: _ => x
        end
    | S p' => nth_default default p' (tail_default default v)
    end.
End Vector.
