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

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Vectors.Vector.
Import VectorNotations.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat Coq.micromega.Lia.

Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Traversable.
Require Export ExtLib.Data.Monads.IdentityMonad.

Require Cava.ListUtils.

Section traversable.
  Universe u v vF.
  Context {F : Type@{v} -> Type@{vF}}.
  Context {Applicative_F : Applicative F}.
  Context {A : Type@{u}} {B : Type@{v}}.
  Variable f : A -> F B.

  Fixpoint mapT_vector@{} {n} (v : Vector.t A n) : F (Vector.t B n) :=
    match v with
    | nil _ => pure []
    | cons _ x _ xs =>
      ap (ap (pure (fun y ys => @Vector.cons B y _ ys)) (f x))
        (mapT_vector xs)
    end.
End traversable.

Global Instance Traversable_vector@{} {n} : Traversable (fun t => Vector.t t n) :=
{ mapT F Ap A B m := mapT_vector m }.

Local Open Scope vector_scope.

Section Vector.
  Context {A:Type}.
  Local Notation t := (Vector.t).

  Fixpoint reshape {n m}: t A (n * m) -> t (t A m) n :=
    match n as n' return t A (n' * m) -> t (t A m) n' with
    | 0 => fun _ => []
    | S n' => fun v =>
      let '(x, xs) := Vector.splitat (r:=n' * m) m v in
      x :: reshape xs
    end.

  Fixpoint flatten {n m}: t (t A m) n -> t A (n*m) :=
    match n as n' return t (t A m) n' -> t A (n'*m) with
    | 0 => fun _ => []
    | S n' => fun v =>
        let '(x, xs) := uncons v in
        x ++ flatten xs
    end.

  Fixpoint unsnoc {n} : t A (S n) -> (t A n * A) :=
    match n with
    | 0 => fun v => ([], hd v)
    | S n' => fun v =>
               let r := unsnoc (tl v) in
               (hd v :: fst r, snd r)
    end.

  Fixpoint snoc {n} : t A n -> A -> t A (S n) :=
    match n with
    | 0 => fun _ a => (a :: [])
    | S n' => fun v a => (hd v :: snoc (tl v) a)
    end.

  (* avoids the equality rewrites in Coq.Vector.rev *)
  Fixpoint reverse {n} : t A n -> t A n :=
    match n with
    | 0 => fun _ => []
    | S n' => fun xs => snoc (reverse (tl xs)) (hd xs)
    end.
End Vector.

Section Transpose.
  Local Notation t := (Vector.t).
  Fixpoint transpose {A n m} : t (t A n) m -> t (t A m) n :=
    match m with
    | 0 => fun _ => const (nil _) _
    | S m' =>
      fun v : t (t A n) (S m') =>
        map2 (fun x v => cons _ x m' v) (hd v) (transpose (tl v))
    end.

  (* Version of transpose that uses snoc/unsnoc instead of cons/tl *)
  Fixpoint transpose_rev {A n m} : t (t A m) n -> t (t A n) m :=
    match n with
    | O => fun _ => const (nil _) _
    | S n' =>
      fun mat =>
        let r := unsnoc mat in
        map2 snoc (transpose_rev (fst r)) (snd r)
    end.
End Transpose.

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

Fixpoint vseq (start len: nat) : Vector.t nat len :=
  match len with
  | 0 => []
  | S n' => start :: vseq (start + 1) n'
  end%vector.


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

  Lemma to_list_resize_default n m (v : t A n) d :
    n = m ->
    to_list (resize_default d m v) = to_list v.
  Proof.
    intros; subst; rewrite resize_default_id. reflexivity.
  Qed.
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

  Lemma fold_left_ext {A B} (f g : B -> A -> B) n b v :
    (forall b a, f b a = g b a) ->
    @Vector.fold_left A B f b n v = Vector.fold_left g b v.
  Proof.
    intro Hfg. revert b.
    induction n; intros; rewrite ?fold_left_0, ?fold_left_S;
      [ reflexivity | ].
    rewrite IHn, Hfg. reflexivity.
  Qed.

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

  Lemma nil_eq {A} (v1 v2 : t A 0) : v1 = v2.
  Proof.
    eapply case0 with (v:=v1).
    eapply case0 with (v:=v2).
    reflexivity.
  Qed.

  Local Ltac vnil :=
    intros;
    repeat
      match goal with
      | |- @eq (t _ 0) _ _ => apply nil_eq
      | vec : t _ 0 |- _ =>
        match goal with
        | |- context [vec] =>
          eapply case0 with (v:=vec);
          clear vec
        end
      | vec : t _ 1 |- _ =>
        match goal with
        | |- context [tl vec] =>
          eapply case0 with (v:=tl vec)
        end
      end.

  Lemma tl_cons {A} n (v : t A n) x :
    tl (cons _ x _ v) = v.
  Proof. reflexivity. Qed.

  Lemma hd_cons {A} n (v : t A n) x :
    hd (cons _ x _ v) = x.
  Proof. reflexivity. Qed.

  Hint Rewrite @tl_cons @hd_cons using solve [eauto] : vsimpl.

  Lemma eta_snoc {A n} (v : t A (S n)) :
    v = snoc (fst (unsnoc v)) (snd (unsnoc v)).
  Proof.
    revert v; induction n.
    { intro v; rewrite (eta v).
      vnil. reflexivity. }
    { intros; cbn [snoc unsnoc fst snd].
      autorewrite with vsimpl. rewrite <-IHn, <-eta.
      reflexivity. }
  Qed.

  Lemma unsnoc_snoc {A n} (v : t A n) x : unsnoc (snoc v x) = (v, x).
  Proof.
    revert v x; induction n; [ vnil; reflexivity | ].
    intros; cbn [snoc unsnoc]. rewrite hd_cons, tl_cons.
    rewrite !IHn. cbn [fst snd]. rewrite <-eta; reflexivity.
  Qed.

  Lemma snoc_const {A} n (x : A) : snoc (const x n) x = const x (S n).
  Proof.
    induction n; intros; [ reflexivity | ].
    cbn [const nat_rect snoc].
    autorewrite with vsimpl. rewrite IHn.
    reflexivity.
  Qed.

  Lemma unsnoc_const {A} n (x : A) : unsnoc (const x (S n)) = (const x n, x).
  Proof.
    induction n; intros; [ reflexivity | ].
    rewrite <-snoc_const with (n0:=S n).
    rewrite unsnoc_snoc. reflexivity.
  Qed.

  Lemma snoc_cons_comm {A} n (x y : A) v :
    snoc (cons _ y n v) x = cons _ y _ (snoc v x).
  Proof. reflexivity. Qed.

  Lemma unsnoc_cons_comm {A} n (x : A) v :
    unsnoc (cons _ x (S n) v) =
    (cons _ x _ (fst (unsnoc v)), snd (unsnoc v)).
  Proof. reflexivity. Qed.

  Lemma unsnoc_tl {A} n (v : t A (S (S n))) :
    unsnoc (tl v) = (tl (fst (unsnoc v)), snd (unsnoc v)).
  Proof. destruct n; reflexivity. Qed.

  Lemma map_0 A B (f : A -> B) (v : t A 0) :
    map f v = nil B.
  Proof. vnil. Qed.
  Hint Rewrite @map_0 using solve [eauto] : vsimpl.

  Lemma map_cons A B n (f : A -> B) v :
    map f v = cons _ (f (hd v)) n
                                 (map f (tl v)).
  Proof. rewrite (eta v). reflexivity. Qed.

  Lemma map2_0 A B C (f : A -> B -> C) (va : t A 0) (vb : t B 0) :
    map2 f va vb = nil C.
  Proof. vnil. Qed.
  Hint Rewrite @map2_0 using solve [eauto] : vsimpl.

  Lemma map2_cons A B C n (f : A -> B -> C) va vb :
    map2 f va vb = cons _ (f (hd va) (hd vb)) n
                                      (map2 f (tl va)
                                                   (tl vb)).
  Proof. rewrite (eta va), (eta vb). reflexivity. Qed.

  Lemma snoc_map2 {A B C n} (f : A -> B -> C) (v1 : t A n) v2 x1 x2 :
    snoc (map2 f v1 v2) (f x1 x2) =  map2 f (snoc v1 x1) (snoc v2 x2).
  Proof.
    revert v1 v2 x1 x2; induction n; [ vnil; reflexivity | ].
    cbn [snoc]; intros.
    repeat first [ rewrite map2_cons
                 | rewrite IHn
                 | progress autorewrite with vsimpl
                 | reflexivity ].
  Qed.

  Lemma unsnoc_map2 {A B C n} (f : A -> B -> C) (v1 : t A (S n)) v2 :
    unsnoc (map2 f v1 v2) = (map2 f (fst (unsnoc v1)) (fst (unsnoc v2)),
                             f (snd (unsnoc v1)) (snd (unsnoc v2))).
  Proof.
    revert v1 v2; induction n.
    { intros v1 v2. rewrite (eta v1), (eta v2).
      vnil. reflexivity. }
    { cbn [unsnoc fst snd]; intros.
      repeat first [ progress cbn [fst snd]
                   | rewrite unsnoc_tl
                   | rewrite map2_cons with (n:=S _)
                   | rewrite IHn
                   | rewrite unsnoc_cons_comm
                   | progress autorewrite with vsimpl
                   | reflexivity ]. }
  Qed.

  Lemma map2_snoc_unsnoc A B C n (f : A -> B -> C) (va : t _ (S n)) vb :
    map2 f va vb = snoc (map2 f (fst (unsnoc va)) (fst (unsnoc vb)))
                                (f (snd (unsnoc va)) (snd (unsnoc vb))).
  Proof.
    induction n; cbn [snoc]; rewrite map2_cons; [ solve [f_equal; vnil] | ].
    rewrite IHn at 1. autorewrite with vsimpl. reflexivity.
  Qed.

  Lemma reverse_const {A} n (x : A) : reverse (const x n) = const x n.
  Proof.
    induction n; intros; [ reflexivity | ].
    cbn [const nat_rect reverse tl caseS].
    rewrite IHn, snoc_const. reflexivity.
  Qed.

  Lemma snoc_reverse {A} n (v : t A n) x :
    snoc (reverse v) x = reverse (cons _ x _ v).
  Proof. reflexivity. Qed.

  Lemma reverse_cons {A} n (v : t A (S n)) :
    reverse v = snoc (reverse (tl v)) (hd v).
  Proof. reflexivity. Qed.

  Lemma reverse_snoc {A} n (v : t A n) x :
    reverse (snoc v x) = cons _ x _ (reverse v).
  Proof.
    induction n; intros; [ vnil; reflexivity | ].
    rewrite !reverse_cons with (n0:=S n).
    cbn [snoc tl hd caseS].
    rewrite IHn. autorewrite with vsimpl.
    rewrite <-snoc_cons_comm.
    reflexivity.
  Qed.

  Lemma hd_reverse_unsnoc {A} n (v : t A (S n)) :
    hd (reverse v) = snd (unsnoc v).
  Proof.
    induction n; [ reflexivity | ].
    rewrite reverse_cons.
    cbn [snoc tl hd caseS].
    rewrite IHn. reflexivity.
  Qed.

  Lemma tl_reverse_unsnoc {A} n (v : t A (S n)) :
    tl (reverse v) = reverse (fst (unsnoc v)).
  Proof.
    induction n; [ reflexivity | ].
    rewrite reverse_cons.
    cbn [snoc tl hd caseS].
    rewrite IHn. reflexivity.
  Qed.

  Lemma reverse_map2 {A B C} n (f : A -> B -> C) va vb :
    reverse (map2 (n:=n) f va vb) = map2 f (reverse va) (reverse vb).
  Proof.
    induction n; intros; [ autorewrite with vsimpl; reflexivity | ].
    rewrite map2_snoc_unsnoc. rewrite map2_cons. autorewrite with vsimpl.
    rewrite reverse_snoc, IHn.
    rewrite !tl_reverse_unsnoc, !hd_reverse_unsnoc.
    reflexivity.
  Qed.

  Lemma map_map2 {A B C D} n (f : A -> B -> C) (g : C -> D) (va : t A n) vb:
    map g (map2 f va vb) = map2 (fun a b => g (f a b)) va vb.
  Proof.
    induction n; intros; autorewrite with vsimpl; [ reflexivity | ].
    rewrite !map_cons, !map2_cons; autorewrite with vsimpl.
    rewrite IHn. reflexivity.
  Qed.

  Lemma map2_append {A B C} (f : A -> B -> C) n m
        (va1 : t A n) (va2 : t A m) vb1 vb2 :
    (map2 f (va1 ++ va2) (vb1 ++ vb2) = map2 f va1 vb1 ++ map2 f va2 vb2)%vector.
  Proof.
    revert m va1 va2 vb1 vb2. induction n; intros.
    { eapply case0 with (v:=va1).
      eapply case0 with (v:=vb1).
      reflexivity. }
    { cbn [Nat.add]. rewrite (eta va1), (eta vb1).
      rewrite <-!append_comm_cons.
      rewrite !map2_cons, ?hd_cons, ?tl_cons.
      rewrite IHn. reflexivity. }
  Qed.

  Lemma map2_flatten {A B C} (f : A -> B -> C) n m
        (va : t (t A n) m) (vb : t (t B n) m) :
    map2 f (flatten va) (flatten vb) = flatten (map2 (map2 f) va vb).
  Proof.
    revert va vb; induction m; intros; [ apply nil_eq | ].
    cbn [flatten Nat.mul]. rewrite (eta va), (eta vb).
    rewrite !uncons_cons.
    rewrite !map2_cons, ?hd_cons, ?tl_cons.
    rewrite map2_append.
    rewrite IHm. reflexivity.
  Qed.

  Lemma hd_snoc {A} n (v : t A (S n)) x :
    hd (snoc v x) = hd v.
  Proof. rewrite (eta v). reflexivity. Qed.

  Lemma map2_ext {A B C} n (f g : A -> B -> C) (va : t A n) vb :
    (forall a b, f a b = g a b) ->
    map2 f va vb = map2 g va vb.
  Proof.
    intros; induction n; [ solve [vnil] | ].
    rewrite !map2_cons. congruence.
  Qed.

  Lemma map2_swap {A B C} n (f : A -> B -> C) (va : t A n) vb :
    map2 f va vb = map2 (fun b a => f a b) vb va.
  Proof.
    intros; induction n; [ solve [vnil] | ].
    rewrite !map2_cons; congruence.
  Qed.

  Lemma map_id_ext {A} (f : A -> A) n (v : t A n) :
    (forall a, f a = a) -> map f v = v.
  Proof.
    intro Hf; induction n; [ solve [vnil] | ].
    rewrite map_cons, Hf, IHn.
    rewrite <-(eta v); congruence.
  Qed.
  Hint Rewrite @map_id_ext
       using solve [intros; autorewrite with vsimpl; reflexivity] : vsimpl.

  Lemma map2_const {A B C} (f : A -> B -> C) n a vb :
    map2 f (const a n) vb = map (f a) vb.
  Proof.
    induction n; [ solve [vnil] | ].
    rewrite map2_cons, map_cons, IHn.
    reflexivity.
  Qed.

  Lemma map2_map {A B C D E} n (f : A -> C) (g : B -> D) (h : C -> D -> E) (va : t A n) vb:
    map2 h (map f va) (map g vb) = map2 (fun a b => h (f a) (g b)) va vb.
  Proof.
    induction n; intros; autorewrite with vsimpl; [ reflexivity | ].
    rewrite !map_cons, !map2_cons; autorewrite with vsimpl.
    rewrite IHn. reflexivity.
  Qed.

  Lemma map2_drop {A B C} (f : A -> C) n va (vb : t B n) :
    map2 (fun a _ => f a) va vb = map f va.
  Proof.
    induction n; intros; [ solve [vnil] | ].
    rewrite map2_cons, map_cons. congruence.
  Qed.

  Lemma map2_drop_same {A B} (f : A -> A -> B) (n : nat) (v : t A n) :
    Vector.map2 f v v = Vector.map (fun x => f x x) v.
  Proof.
    induction v; [ reflexivity | ].
    cbn [Vector.map]. rewrite <-IHv.
    reflexivity.
  Qed.

  Lemma map_to_const {A B} (n : nat) (v : t A n) (b : B) :
    Vector.map (fun _ => b) v = Vector.const b n.
  Proof.
    induction v; [ reflexivity | ].
    cbn [Vector.map]. rewrite IHv.
    reflexivity.
  Qed.

  Lemma snoc_map {A B n} (f : A -> B) (v : t A n) x :
    snoc (map f v) (f x) =  map f (snoc v x).
  Proof.
    revert v x; induction n; [ vnil; reflexivity | ].
    cbn [snoc]; intros.
    repeat first [ rewrite map_cons
                 | rewrite IHn
                 | progress autorewrite with vsimpl
                 | reflexivity ].
  Qed.

  Lemma unsnoc_map {A B n} (f : A -> B) (v : t A (S n)) :
    unsnoc (map f v) = (map f (fst (unsnoc v)), f (snd (unsnoc v))).
  Proof.
    revert v; induction n.
    { intros v. rewrite (eta v). vnil; reflexivity. }
    { cbn [unsnoc fst snd]; intros.
      repeat first [ progress cbn [fst snd]
                   | rewrite unsnoc_tl
                   | rewrite map_cons with (n:=S _)
                   | rewrite IHn
                   | rewrite unsnoc_cons_comm
                   | progress autorewrite with vsimpl
                   | reflexivity ]. }
  Qed.

  Lemma map_snoc_unsnoc {A B n} (f : A -> B) (v : t A (S n)) :
    map f v = snoc (map f (fst (unsnoc v))) (f (snd (unsnoc v))).
  Proof.
    induction n; intros; cbn [snoc unsnoc map fst snd];
      repeat first [ rewrite map_cons
                   | rewrite <-IHn
                   | progress autorewrite with vsimpl
                   | reflexivity ].
  Qed.

  Lemma fold_left_andb_true (n : nat) :
    Vector.fold_left andb true (Vector.const true n) = true.
  Proof.
    induction n; [ reflexivity | ].
    etransitivity; [ | apply IHn ].
    reflexivity.
  Qed.

  Lemma fold_left_andb_false (n : nat) (v : t bool n) :
    Vector.fold_left andb false v = false.
  Proof. induction v; auto. Qed.

  Lemma fold_left_fst_unchanged {A B C} (f : B * C -> A -> B * C) bc n (v : t A n) :
    (forall bc a, fst (f bc a) = fst bc) ->
    Vector.fold_left f bc v = (fst bc, Vector.fold_left
                                         (fun c a => snd (f (fst bc,c) a)) (snd bc) v).
  Proof.
    intro Hfstf. revert bc v.
    induction n; intros; autorewrite with push_vector_fold;
      [ destruct bc; reflexivity | ].
    rewrite IHn, Hfstf, <-surjective_pairing.
    reflexivity.
  Qed.

  Lemma to_list_nil {A} : to_list (Vector.nil A) = List.nil.
  Proof. reflexivity. Qed.
  Lemma to_list_cons {A n} a (v : t A n) :
    to_list (a :: v)%vector = a :: to_list v.
  Proof. reflexivity. Qed.
  Hint Rewrite @to_list_nil @to_list_cons using solve [eauto] : vsimpl.

  Lemma to_list_append {A n m} (v1 : t A n) (v2 : t A m) :
    to_list (v1 ++ v2)%vector = to_list v1 ++ to_list v2.
  Proof.
    revert v2; induction v1; [ reflexivity | ].
    intros. rewrite <-append_comm_cons.
    cbn [Nat.add]. autorewrite with vsimpl.
    rewrite <-app_comm_cons, IHv1.
    reflexivity.
  Qed.

  Lemma to_list_length {A n} (v : t A n) :
    length (to_list v) = n.
  Proof.
    induction v; [ reflexivity | ].
    autorewrite with vsimpl.
    cbn [length].
    congruence.
  Qed.

  Lemma to_list_map {A B} (f : A -> B) n (v : t A n) :
    to_list (map f v) = List.map f (to_list v).
  Proof.
    induction n; intros; [ vnil; reflexivity | ].
    rewrite (eta v). rewrite map_cons.
    autorewrite with vsimpl. cbn [List.map].
    rewrite IHn; reflexivity.
  Qed.

  Lemma fold_left_to_list {A B} (f : B -> A -> B) n b (v : t A n) :
    fold_left f b v = List.fold_left f (to_list v) b.
  Proof.
    revert b; induction v; intros; [ reflexivity | ].
    autorewrite with vsimpl. cbn [List.fold_left].
    rewrite IHv; reflexivity.
  Qed.

  Lemma const_cons {A n} (a : A) :
    const a (S n) = Vector.cons _ a _ (const a n).
  Proof. reflexivity. Qed.

  Lemma const_nil {A n} (v : t (t A 0) n) : v = const (nil _) _.
  Proof.
    revert v; induction n; [ solve [vnil] | ].
    intro v; rewrite (eta v). eapply case0 with (v:=hd v).
    rewrite (IHn (tl v)); reflexivity.
  Qed.
End VectorFacts.
(* These hints create and populate the following autorewrite databases:
 * - push_vector_fold : simplify using properties of Vector.fold_left
 * - push_vector_tl_hd_last : simplify using properties of Vector.tl, Vector.hd,
     and Vector.last
 * - push_vector_nth_order : simplify expressions containing Vector.nth_order
 * - push_vector_map : simplify expressions containing Vector.map or Vector.map2
 * - vsimpl : generic vector simplification, includes all of the above and more
 *
 * No hint added to one of these databases should leave any subgoals unsolved.
 *)
Hint Rewrite @fold_left_0
     using solve [eauto] : push_vector_fold vsimpl.
Hint Rewrite @tl_0 @hd_0 @tl_cons @hd_cons @last_tl
     using solve [eauto] : push_vector_tl_hd_last vsimpl.
Hint Rewrite @nth_order_hd @nth_order_last
     using solve [eauto] : push_vector_nth_order vsimpl.
Hint Rewrite @map2_0 @map_0 @map_to_const @map2_append
     using solve [eauto] : push_vector_map vsimpl.
Hint Rewrite @resize_default_id @Vector.map_id
     using solve [eauto] : vsimpl.
Hint Rewrite @to_list_cons @to_list_nil @uncons_cons
     using solve [eauto] : vsimpl.


(* Lemmas that work on any (S _) length don't get added to vsimpl, because
   they can end up happening many times for constant-length expressions *)
Hint Rewrite @fold_left_S
     using solve [eauto] : push_vector_fold.
Hint Rewrite @map_cons @map2_cons
     using solve [eauto] : push_vector_map.

(* Some extra lemmas that don't necessarily make a goal *simpler*, but do push a
   certain kind of operation deeper into the expression, go into the push_*
   databases *)
Hint Rewrite <- @reverse_map2 @snoc_map2 @unsnoc_map2 @snoc_map @unsnoc_map
     using solve [eauto] : push_vector_map.
Hint Rewrite  @nth_map @map_to_const @map2_flatten
     using solve [eauto] : push_vector_map.

(* [eauto] might not solve map_id_ext, so add more power to the strategy *)
Hint Rewrite @map_id_ext
     using solve [intros; autorewrite with vsimpl; eauto]
  : push_vector_map vsimpl.

(* Hints to change a goal from vectors to list go in the vec_to_list database *)
Hint Rewrite @to_list_nil @to_list_cons @to_list_append
     @fold_left_to_list @to_list_map @to_list_of_list_opp
     using solve [eauto] : push_to_list.
Hint Rewrite @to_list_resize_default
     using solve [ListUtils.length_hammer] : push_to_list.
Hint Rewrite @to_list_length using solve [eauto] : push_length.

Section VcombineFacts.
  Lemma to_list_vcombine {A B n} (v1 : Vector.t A n) (v2 : Vector.t B n) :
    to_list (vcombine v1 v2) = combine (to_list v1) (to_list v2).
  Proof.
    induction n; intros.
    { eapply case0 with (v:=v1). eapply case0 with (v:=v2).
      reflexivity. }
    { rewrite (eta v1), (eta v2).
      cbn [vcombine].
      rewrite !uncons_cons, !to_list_cons.
      cbn [combine]. rewrite IHn; reflexivity. }
  Qed.
End VcombineFacts.
Hint Rewrite @to_list_vcombine using solve [eauto] : push_to_list.

Section VseqFacts.
  Lemma vseq_S start len :
    vseq start (S len) = (start :: vseq (S start) len)%vector.
  Proof. cbv [vseq]. rewrite Nat.add_1_r. reflexivity. Qed.

  Lemma to_list_vseq start len : to_list (vseq start len) = List.seq start len.
  Proof.
    revert start; induction len; [ reflexivity | ].
    intros; rewrite vseq_S. cbn [seq].
    autorewrite with push_to_list.
    rewrite IHlen; reflexivity.
  Qed.
End VseqFacts.
Hint Rewrite @to_list_vseq using solve [eauto] : push_to_list.

Section TransposeFacts.
  Local Notation t := Vector.t.

  Lemma snoc_transpose_rev {A n m} (v : t (t A n) m) (x : t A m) :
    snoc (transpose_rev v) x = transpose_rev (map2 snoc v x).
  Proof.
    revert n v x; induction m; intros; cbn [transpose_rev].
    { rewrite <-snoc_const. f_equal; apply nil_eq. }
    { let x := match goal with x : t A (S _) |- _ => x end in
      rewrite (eta_snoc x), snoc_map2, <-(eta_snoc x).
      rewrite unsnoc_map2. cbn [fst snd].
      rewrite IHm. reflexivity. }
  Qed.

  Lemma unsnoc_transpose_rev {A n m} (v : t (t A (S n)) m) :
    unsnoc (transpose_rev v) = (transpose_rev (map (fun x => fst (unsnoc x)) v),
                                map (fun x => snd (unsnoc x)) v).
  Proof.
    revert n v; induction m; intros; cbn [transpose_rev].
    { rewrite unsnoc_const. f_equal; apply nil_eq. }
    { rewrite unsnoc_map2. rewrite IHm. cbn [fst snd].
      rewrite unsnoc_map, map_snoc_unsnoc. cbn [fst snd].
      reflexivity. }
  Qed.

  Lemma transpose_rev_involutive {A n m} (v : t (t A n) m) :
    transpose_rev (transpose_rev v) = v.
  Proof.
    revert n v; induction m; intros; [ solve [apply nil_eq] | ].
    destruct n; cbn [transpose_rev];
      [ rewrite (const_nil v); reflexivity | ].
    rewrite (eta_snoc v).
    rewrite unsnoc_snoc, unsnoc_map2. cbn [fst snd].
    rewrite <-snoc_transpose_rev, unsnoc_transpose_rev.
    cbn [fst snd]. rewrite IHm. rewrite <-snoc_map2, <-eta_snoc.
    rewrite map2_map, map2_drop_same, map_id_ext
      by (intros; rewrite <-eta_snoc; reflexivity).
    reflexivity.
  Qed.
End TransposeFacts.

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

  Definition of_list_sized {A} (a : A) (n : nat) (l : list A) : Vector.t A n :=
    resize_default a  _ (Vector.of_list l).
End Vector.
