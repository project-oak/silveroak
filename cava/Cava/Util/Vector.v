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

Require Cava.Util.List.

(* automatically interpret arguments expected to have type Vector.t in
   vector_scope *)
Bind Scope vector_scope with Vector.t.

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

  Fixpoint unfold {n A B} (b:B) (f : B -> A*B) : t A n
    := match n with
       | 0 => []
       | S n' => let (a,b) := f b in a :: unfold b f end.

  Fixpoint unfold_ix {n A B} (b:B) (f : nat -> B -> A*B) : t A n
    := match n with
       | 0 => []
       | S n' => let (a,b) := f n' b in a :: unfold_ix b f end.

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

Definition vcombine {A B: Type} {s: nat} (a: Vector.t A s) (b: Vector.t B s) :
  Vector.t (A * B) s :=
  Vector.map2 (fun a b => (a,b)) a b.

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
  (match l return AltVector A (length l)  with
   | [] => tt
   | x::xs => vec_cons (consAltVector x (listToAltVector xs))
   end)%list.

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

  Lemma resize_default_resize_default n m p (v : t A n) d :
    n = m -> resize_default d p (resize_default d m v) = resize_default d p v.
  Proof. intros; subst. rewrite resize_default_id. reflexivity. Qed.

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

  Hint Rewrite @fold_left_S @fold_left_0
       using solve [eauto] : push_vector_fold vsimpl.

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

  Lemma const_cons {A n} (a : A) :
    const a (S n) = Vector.cons _ a _ (const a n).
  Proof. reflexivity. Qed.

  Lemma const_nil {A n} (v : t (t A 0) n) : v = const (nil _) _.
  Proof.
    revert v; induction n; [ solve [vnil] | ].
    intro v; rewrite (eta v). eapply case0 with (v:=hd v).
    rewrite (IHn (tl v)); reflexivity.
  Qed.

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

  Lemma shiftout_cons {A} n x (v : Vector.t A (S n)) :
    shiftout (x :: v) = x :: shiftout v.
  Proof. reflexivity. Qed.

  Lemma shiftout_const {A} n (x : A) :
    shiftout (const x (S n)) = const x n.
  Proof.
    induction n; [ reflexivity | ].
    rewrite const_cons, shiftout_cons.
    rewrite IHn; reflexivity.
  Qed.

  Lemma last_cons {A} n x (v : Vector.t A (S n)) :
    Vector.last (x :: v) = Vector.last v.
  Proof. reflexivity. Qed.

  Lemma last_const {A} n (x : A) :
    Vector.last (const x (S n)) = x.
  Proof.
    induction n; [ reflexivity | ].
    rewrite const_cons, last_cons, IHn.
    reflexivity.
  Qed.

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

  Lemma map2_splitat1 {A B C} (f : A -> B -> C) n m (va : Vector.t A (n + m)) vb :
    map2 f (fst (splitat _ va)) (fst (splitat _ vb))
    = fst (splitat _ (map2 f va vb)).
  Proof.
    erewrite append_splitat with (vw:=va) by apply surjective_pairing.
    erewrite append_splitat with (vw:=vb) by apply surjective_pairing.
    rewrite map2_append, !splitat_append. cbn [fst snd].
    reflexivity.
  Qed.

  Lemma map2_splitat2 {A B C} (f : A -> B -> C) n m (va : Vector.t A (n + m)) vb :
    map2 f (snd (splitat _ va)) (snd (splitat _ vb))
    = snd (splitat _ (map2 f va vb)).
  Proof.
    erewrite append_splitat with (vw:=va) by apply surjective_pairing.
    erewrite append_splitat with (vw:=vb) by apply surjective_pairing.
    rewrite map2_append, !splitat_append. cbn [fst snd].
    reflexivity.
  Qed.

  Lemma map2_reshape {A B C} (f : A -> B -> C) n m
        (va : t A (n * m)) (vb : t B (n * m)) :
    map2 (map2 f) (reshape va) (reshape vb) = reshape (map2 f va vb).
  Proof.
    revert va vb; induction n; intros; [ apply nil_eq | ].
    cbn [reshape].
    repeat match goal with
           | |- context [match ?p with pair _ _ => _ end] =>
             rewrite (surjective_pairing p)
           end.
    rewrite !map2_cons, ?hd_cons, ?tl_cons.
    rewrite IHn, map2_splitat1, map2_splitat2.
    reflexivity.
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

  Lemma reverse_map {A B} n (f : A -> B) v :
    reverse (map (n:=n) f v) = map f (reverse v).
  Proof.
    induction n; intros; [ autorewrite with vsimpl; reflexivity | ].
    rewrite (eta v). cbn [map reverse]. autorewrite with vsimpl.
    rewrite IHn. rewrite snoc_map. reflexivity.
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
    to_list (a :: v) = (a :: to_list v)%list.
  Proof. reflexivity. Qed.
  Hint Rewrite @to_list_nil @to_list_cons using solve [eauto] : vsimpl.

  Lemma to_list_append {A n m} (v1 : t A n) (v2 : t A m) :
    to_list (v1 ++ v2) = (to_list v1 ++ to_list v2)%list.
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

  Lemma to_list_inj {A n} (v1 v2 : t A n) :
    to_list v1 = to_list v2 -> v1 = v2.
  Proof.
    revert v1 v2; induction n; [ intros; apply nil_eq | ].
    intros v1 v2; rewrite (Vector.eta v1), (Vector.eta v2) in *.
    rewrite !to_list_cons; intros.
    match goal with H : (_ :: _)%list = _ |- _ => inversion H; clear H end.
    f_equal; auto.
  Qed.

  Lemma to_list_splitat1 {A} n m (v : Vector.t A (n + m)) :
    to_list (fst (splitat _ v)) = firstn n (to_list v).
  Proof.
    erewrite append_splitat with (vw:=v) by apply surjective_pairing.
    rewrite splitat_append, to_list_append. cbn [fst snd].
    autorewrite with push_firstn. rewrite to_list_length.
    autorewrite with natsimpl push_firstn listsimpl.
    rewrite firstn_all2 by (rewrite to_list_length; reflexivity).
    reflexivity.
  Qed.

  Lemma to_list_splitat2 {A} n m (v : Vector.t A (n + m)) :
    to_list (snd (splitat _ v)) = skipn n (to_list v).
  Proof.
    erewrite append_splitat with (vw:=v) by apply surjective_pairing.
    rewrite splitat_append, to_list_append. cbn [fst snd].
    autorewrite with push_skipn. rewrite to_list_length.
    autorewrite with natsimpl push_skipn listsimpl.
    rewrite skipn_all2 by (rewrite to_list_length; reflexivity).
    reflexivity.
  Qed.

  Lemma to_list_snoc {A n} (v : Vector.t A n) x :
    to_list (snoc v x) = (to_list v ++ [x])%list.
  Proof.
    revert v; induction n; [ vnil; reflexivity | ].
    intros; rewrite (eta v). cbn [snoc].
    autorewrite with vsimpl.
    rewrite IHn, app_comm_cons.
    reflexivity.
  Qed.

  Lemma to_list_map2 {A B C} (f : A -> B -> C) n
        (va : Vector.t A n) (vb : Vector.t B n) :
    to_list (map2 f va vb) = List.map2 f (to_list va) (to_list vb).
  Proof.
    revert va vb; induction n; intros.
    { eapply case0 with (v:=va).
      eapply case0 with (v:=vb).
      reflexivity. }
    { rewrite (eta va), (eta vb).
      rewrite map2_cons. autorewrite with vsimpl.
      rewrite IHn. reflexivity. }
  Qed.

  Lemma fold_left_to_list {A B} (f : B -> A -> B) n b (v : t A n) :
    fold_left f b v = List.fold_left f (to_list v) b.
  Proof.
    revert b; induction v; intros; [ reflexivity | ].
    autorewrite with vsimpl. cbn [List.fold_left].
    rewrite IHv; reflexivity.
  Qed.

  Lemma reshape_flatten {A n m} (v : t (t A n) m) :
    reshape (flatten v) = v.
  Proof.
    revert n v. induction m; [ solve [vnil] | ].
    cbn [reshape flatten]; intros. rewrite (eta v).
    rewrite uncons_cons, splitat_append.
    rewrite IHm; reflexivity.
  Qed.

  Lemma flatten_reshape {A n m} (v : t A (m * n)) :
    flatten (reshape v) = v.
  Proof.
    revert n v. induction m; cbn [Nat.mul]; [ solve [vnil] | ].
    intros. cbn [reshape flatten]; intros.
    rewrite (surjective_pairing (splitat _ _)).
    rewrite uncons_cons. rewrite IHm.
    erewrite <-append_splitat; [ reflexivity | ].
    rewrite <-surjective_pairing. reflexivity.
  Qed.

  Lemma map_append {A B} (f : A -> B) n m (v1 : t A n) (v2 : t A m) :
    map f (v1 ++ v2) = map f v1 ++ map f v2.
  Proof.
    revert m v1 v2; induction n; [ vnil; reflexivity | ].
    intros m v1 v2; rewrite (eta v1).
    rewrite <-append_comm_cons. cbn [map].
    rewrite IHn. rewrite <-append_comm_cons.
    reflexivity.
  Qed.

  Lemma map_splitat1 {A B} (f : A -> B) n m (v : Vector.t A (n + m)) :
    map f (fst (splitat _ v)) = fst (splitat _ (map f v)).
  Proof.
    erewrite append_splitat with (vw:=v) by apply surjective_pairing.
    rewrite !map_append, !splitat_append. cbn [fst snd].
    reflexivity.
  Qed.

  Lemma map_splitat2 {A B} (f : A -> B) n m (v : Vector.t A (n + m)) :
    map f (snd (splitat _ v)) = snd (splitat _ (map f v)).
  Proof.
    erewrite append_splitat with (vw:=v) by apply surjective_pairing.
    rewrite !map_append, !splitat_append. cbn [fst snd].
    reflexivity.
  Qed.

  Lemma map_reshape {A B n m} (f : A -> B) (v : t A (m * n)) :
    map (map f) (reshape v) = reshape (map f v).
  Proof.
    revert n v; induction m; cbn [Nat.mul]; [ solve [vnil] | ].
    intros. cbn [reshape].
    repeat match goal with
             |- context [match ?p with pair _ _ => _ end] =>
             rewrite (surjective_pairing p)
           end.
    rewrite map_cons. autorewrite with vsimpl.
    rewrite IHm. rewrite map_splitat1, map_splitat2.
    reflexivity.
  Qed.

  Lemma map_flatten {A B} (f : A -> B) (n m : nat) (v : t (t A n) m) :
    map f (flatten v) = flatten (map (map f) v).
  Proof.
    revert n v; induction m; cbn [Nat.mul]; [ vnil; reflexivity | ].
    intros; rewrite (eta v). cbn [flatten uncons].
    rewrite !map_cons. autorewrite with vsimpl.
    rewrite map_append. rewrite IHm. reflexivity.
  Qed.

  Lemma reverse_reverse {A n} (v : t A n) :
    reverse (reverse v) = v.
  Proof.
    revert v; induction n; [ solve [vnil] | ].
    intros. rewrite (eta_snoc v).
    rewrite reverse_snoc. cbn [reverse].
    autorewrite with vsimpl. rewrite IHn.
    reflexivity.
  Qed.

End VectorFacts.
(* These hints create and populate the following autorewrite databases:
 * - push_vector_fold : simplify using properties of Vector.fold_left
 * - push_vector_tl_hd_last : simplify using properties of Vector.tl, Vector.hd,
     and Vector.last
 * - push_vector_nth_order : simplify expressions containing Vector.nth_order
 * - push_vector_map : push Vector.map or Vector.map2 deeper into the expression
 * - pull_vector_map : pull Vector.map or Vector.map2 to the outside of the expression
 * - vsimpl : generic vector simplification, includes all of the above and more
 *
 * No hint added to one of these databases should leave any subgoals unsolved.
 *)
Hint Rewrite @fold_left_0
     using solve [eauto] : push_vector_fold vsimpl.
Hint Rewrite @tl_0 @tl_cons @hd_cons @last_tl
     using solve [eauto] : push_vector_tl_hd_last vsimpl.
Hint Rewrite @nth_order_hd @nth_order_last
     using solve [eauto] : push_vector_nth_order vsimpl.
Hint Rewrite @map2_0 @map_0 @map_to_const @map2_append @map_append
     using solve [eauto] : push_vector_map vsimpl.
Hint Rewrite <- @map2_append @map_append
     using solve [eauto] : pull_vector_map.
Hint Rewrite @resize_default_id @Vector.map_id
     using solve [eauto] : vsimpl.
Hint Rewrite @to_list_cons @to_list_nil @uncons_cons @reshape_flatten @flatten_reshape
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
Hint Rewrite <- @reverse_map2 @reverse_map @snoc_map2 @unsnoc_map2 @snoc_map @unsnoc_map
     using solve [eauto] : push_vector_map.
Hint Rewrite @nth_map @map2_flatten @map2_reshape @map2_splitat1
     @map2_splitat2 @map_reshape @map_splitat1 @map_splitat2 @map_flatten
     using solve [eauto] : push_vector_map.

(* Reverse rewrites for pull_* *)
Hint Rewrite @reverse_map2 @reverse_map @snoc_map2 @unsnoc_map2 @snoc_map @unsnoc_map
     using solve [eauto] : pull_vector_map.
Hint Rewrite <- @map2_flatten @map2_reshape @map2_splitat1 @map2_splitat2
     @map_reshape @map_splitat1 @map_splitat2 @map_flatten
     using solve [eauto] : pull_vector_map.

(* [eauto] might not solve map_id_ext, so add more power to the strategy *)
Hint Rewrite @map_id_ext
     using solve [intros; autorewrite with vsimpl; eauto]
  : push_vector_map vsimpl.

(* Hints to change a goal from vectors to list go in the push_to_list database *)
Hint Rewrite @to_list_nil @to_list_cons @to_list_append
     @fold_left_to_list @to_list_map @to_list_of_list_opp
     @to_list_splitat1 @to_list_splitat2 @to_list_snoc @to_list_map2
     using solve [eauto] : push_to_list.
Hint Rewrite @to_list_resize_default
     using solve [List.length_hammer] : push_to_list.
Hint Rewrite @to_list_length using solve [eauto] : push_length.

Section VcombineFacts.
  Lemma to_list_vcombine {A B n} (v1 : Vector.t A n) (v2 : Vector.t B n) :
    to_list (vcombine v1 v2) = combine (to_list v1) (to_list v2).
  Proof.
    cbv [vcombine].
    induction n; intros.
    { eapply case0 with (v:=v1). eapply case0 with (v:=v2).
      reflexivity. }
    { rewrite (eta v1), (eta v2).
      autorewrite with push_vector_map vsimpl.
      cbn [combine].
      rewrite IHn; reflexivity. }
  Qed.

  Lemma map_vcombine_map2 {A B C n} (f : A * B -> C)
        (va : Vector.t A n) (vb : Vector.t B n) :
    map f (vcombine va vb) = Vector.map2 (fun a b => f (a,b)) va vb.
  Proof.
    cbv [vcombine]. rewrite map_map2. reflexivity.
  Qed.

  Lemma vcombine_cons {A B n} (va : Vector.t A n) (vb : Vector.t B n) a b :
    vcombine (a :: va)%vector (b :: vb)%vector = ((a,b) :: vcombine va vb)%vector.
  Proof.
    cbv [vcombine]; autorewrite with push_vector_map vsimpl.
    reflexivity.
  Qed.

  Lemma vcombine_nil {A B} (va : Vector.t A 0) (vb : Vector.t B 0) :
    vcombine va vb = Vector.nil _.
  Proof. apply nil_eq. Qed.
End VcombineFacts.
Hint Rewrite @to_list_vcombine using solve [eauto] : push_to_list.
Hint Rewrite @vcombine_cons @vcombine_nil using solve [eauto] : push_vcombine.

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

  Lemma cons_transpose {A n m} (v : t (t A n) m) (x : t A m) :
    x :: transpose v = transpose (map2 (fun a v => a :: v) x v).
  Proof.
    revert n v x; induction m; intros; cbn [transpose].
    { eapply case0 with (v:=x). reflexivity. }
    { rewrite map2_cons with (va:=x).
      autorewrite with vsimpl. rewrite <-IHm.
      rewrite map2_cons. autorewrite with vsimpl.
      rewrite <-(eta x). reflexivity. }
  Qed.

  Lemma transpose_cons {A n m} (v : t (t A (S n)) m) :
    transpose v = (map hd v :: transpose (map tl v))%vector.
  Proof.
    revert n v; induction m; intros; cbn [transpose].
    { eapply case0 with (v:=map hd v). reflexivity. }
    { rewrite map2_cons. autorewrite with vsimpl.
      rewrite IHm.
      autorewrite with vsimpl push_vector_map.
      reflexivity. }
  Qed.

  Lemma transpose_involutive {A n m} (v : t (t A n) m) :
    transpose (transpose v) = v.
  Proof.
    revert n v; induction m; intros; [ solve [apply nil_eq] | ].
    destruct n; cbn [transpose];
      [ rewrite (const_nil v); reflexivity | ].
    match goal with |- context [ hd (map2 ?f ?va ?vb) ] =>
                    rewrite (map2_cons _ _ _ _ f va vb)
    end.
    autorewrite with vsimpl.
    rewrite <-cons_transpose, transpose_cons.
    autorewrite with vsimpl.
    rewrite IHm.
    rewrite <-!map_cons, map2_map, map2_drop_same.
    apply map_id_ext; intros.
    rewrite <-eta; reflexivity.
  Qed.

  Lemma transpose_map_map {A B} n m (f: A -> B) (v : Vector.t (Vector.t A n) m) :
    transpose (map (map f) v) = map (map f) (transpose v).
  Proof.
    revert n v; induction m; intros; [ symmetry; solve [apply const_nil] | ].
    destruct n; cbn [transpose]; [ solve [apply nil_eq] | ].
    autorewrite with push_vector_map vsimpl.
    rewrite IHm. autorewrite with push_vector_map vsimpl.
    rewrite map2_map, map_map2.
    reflexivity.
  Qed.

  (* Helper lemma for transpose_map2_map2 *)
  Lemma transpose_map2_map2_helper {A B C n m} (f : A -> B -> C)
        (va : Vector.t A n) vb (vva : Vector.t (Vector.t A m) n) vvb :
    map2 (fun x v => x :: v) (map2 f va vb) (map2 (map2 f) vva vvb)
    = map2 (map2 f) (map2 (fun x v => x :: v) va vva) (map2 (fun x v => x :: v) vb vvb).
  Proof.
    revert va vb vva vvb; induction n; intros; [ solve [apply nil_eq] | ].
    autorewrite with push_vector_map vsimpl.
    rewrite IHn. reflexivity.
  Qed.

  Lemma transpose_map2_map2 {A B C} n m (f: A -> B -> C)
        (va : Vector.t (Vector.t A n) m) vb:
    transpose (map2 (map2 f) va vb) = map2 (map2 f) (transpose va) (transpose vb).
  Proof.
    revert n va vb; induction m; intros; [ symmetry; solve [apply const_nil] | ].
    destruct n; cbn [transpose]; [ solve [apply nil_eq] | ].
    autorewrite with push_vector_map vsimpl.
    rewrite IHm. autorewrite with push_vector_map vsimpl.
    f_equal. apply transpose_map2_map2_helper.
  Qed.
End TransposeFacts.
Hint Rewrite @transpose_map_map @transpose_map2_map2
     using solve [eauto] : pull_vector_map.
Hint Rewrite <- @transpose_map_map @transpose_map2_map2
     using solve [eauto] : push_vector_map.

Section InV.
  (* Version of Vector.In that is defined as a computable Prop rather than an
     inductive (similar to List.In). The reason for defining this is that
     Vector.In does not play nicely with [inversion] and requires using the
     EqDep axioms to prove that In x (y :: v) -> y = x \/ In x v. *)
  Fixpoint InV {A n} (x : A) : Vector.t A n -> Prop :=
    match n with
    | 0 => fun _ => False
    | S n' => fun v => x = Vector.hd v \/ InV x (Vector.tl v)
    end.

  Lemma InV_cons_iff {A n} (v : Vector.t A n) (a x : A) :
    InV x (a :: v)%vector <-> (x = a \/ InV x v).
  Proof. reflexivity. Qed.

  Lemma InV_map_iff {A B n} (f : A -> B) (v : Vector.t A n) x :
    InV x (map f v)%vector <-> (exists y, f y = x /\ InV y v).
  Proof.
    revert v; induction n; intros *; [ eapply case0 with (v:=v) | rewrite (eta v) ].
    all:cbn [InV] in *.
    all:autorewrite with push_vector_map vsimpl.
    all:split; intros;
      repeat match goal with
             | H : exists _, _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             | H : _ \/ _ |- _ => destruct H
             | H : InV _ (map _ _) |- _ => rewrite IHn in H
             | _ => progress subst
             | |- exists y, ?f y = ?f ?x /\ _ =>
               exists x; split; [ reflexivity | ];
                 constructor; solve [eauto]
             | |- _ \/ InV _ (map _ _) =>
               rewrite IHn; right; eexists; split; solve [eauto]
             | _ => tauto
             end.
  Qed.

  Lemma InV_map2_impl {A B C n} (f : A -> B -> C) (v1 : Vector.t A n) v2 x :
    InV x (Vector.map2 f v1 v2)%vector -> (exists a b, f a b = x /\ InV a v1 /\ InV b v2).
  Proof.
    revert v1 v2; induction n; intros v1 v2;
      [ eapply case0 with (v:=v1); eapply case0 with (v:=v2);
        cbn [InV]; tauto | ].
    rewrite (eta v1), (eta v2). cbn [InV]; intros.
    repeat match goal with
           | _ => progress subst
           | _ => progress autorewrite with push_vector_map vsimpl in *
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           | H : _ \/ _ |- _ => destruct H
           | H : InV _ (Vector.map2 _ _ _) |- _ => apply IHn in H
           | |- exists x y, ?f x y = ?f ?a ?b /\ _ =>
             exists a, b; repeat split; cbn [InV]; solve [eauto]
           end.
  Qed.

  Lemma InV_to_list_iff {A n} (v : Vector.t A n) x :
    List.In x (to_list v)%vector <-> InV x v.
  Proof.
    revert v; induction n; intros;
      [ eapply case0 with (v:=v); cbn [InV]; tauto | ].
    rewrite (eta v). autorewrite with push_to_list.
    cbn [InV List.In]; intros.
    repeat match goal with
           | _ => progress subst
           | _ => progress autorewrite with push_vector_map vsimpl in *
           | H : exists _, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           | H : _ \/ _ |- _ => destruct H
           | _ => rewrite <-IHn
           | |- _ <-> _ => split; intros
           | |- ?x = ?x \/ _ => left; reflexivity
           | H : ?P |- _ \/ ?P => right; assumption
           end.
  Qed.

  Lemma map_ext_InV {A B n} (f g : A -> B) (v : Vector.t A n) :
    (forall a, InV a v -> f a = g a) -> map f v = map g v.
  Proof.
    revert v; induction n; intros;
      [ eapply case0 with (v:=v); cbn [InV]; tauto | ].
    rewrite (eta v) in *; cbn [InV] in *.
    autorewrite with push_vector_map vsimpl in *.
    f_equal; auto.
  Qed.

  Lemma map2_ext_InV {A B C n} (f g : A -> B -> C) (va : Vector.t A n) vb :
    (forall a b, InV a va -> InV b vb -> f a b = g a b) -> map2 f va vb = map2 g va vb.
  Proof.
    revert va vb; induction n; intros;
      [ eapply case0 with (v:=va); cbn [InV]; tauto | ].
    rewrite (eta va), (eta vb) in *; cbn [InV] in *.
    autorewrite with push_vector_map vsimpl in *.
    f_equal; auto.
  Qed.
End InV.

Section ForallV.
  (* Non-inductive version of Vector.Forall; the standard library version is
     hard to extract information from because it creates existT terms after
     inversion in the cons case *)
  Fixpoint ForallV {A n} (P : A -> Prop) : Vector.t A n -> Prop :=
    match n with
    | 0 => fun _ => True
    | S n' => fun v => P (Vector.hd v) /\ ForallV P (Vector.tl v)
    end.

  Lemma ForallV_forall {A n} P (v : Vector.t A n) :
    ForallV P v <-> (forall x, InV x v -> P x).
  Proof.
    revert v; induction n; intros; cbn [ForallV InV]; [ tauto | ].
    rewrite IHn. split; intros.
    all:repeat match goal with
               | _ => progress subst
               | H : _ \/ _ |- _ => destruct H
               | H : _ /\ _ |- _ => destruct H
               | _ => repeat split; solve [eauto]
               end.
  Qed.

  Lemma ForallV_append {A n m} P (v1 : Vector.t A n) (v2 : Vector.t A m) :
    ForallV P (v1 ++ v2) <-> (ForallV P v1 /\ ForallV P v2).
  Proof.
    revert v1 v2; induction n; intros v1 v2.
    { eapply case0 with (v:=v1); cbn [Vector.append ForallV].
      tauto. }
    { rewrite (eta v1). rewrite <-append_comm_cons.
      change (S n + m) with (S (n + m)) in *.
      cbn [ForallV]. autorewrite with vsimpl.
      rewrite IHn; tauto. }
  Qed.

  Lemma ForallV_const {A} n (P : A -> Prop) x :
    P x -> ForallV P (const x n).
  Proof.
    induction n; intros; cbn [ForallV]; [ tauto | ].
    rewrite const_cons. autorewrite with vsimpl. tauto.
  Qed.

  Lemma ForallV_resize {A n} m P (v : Vector.t A n) H :
    ForallV P (resize m H v) <-> ForallV P v.
  Proof. subst. rewrite <-resize_id. reflexivity. Qed.

  Lemma ForallV_trivial {A} n (P : A -> Prop) (v : Vector.t A n) :
    (forall x, P x) -> ForallV P v.
  Proof.
    induction n; intros; cbn [ForallV]; [ tauto | ].
    split; auto.
  Qed.

  Lemma ForallV_splitat1 {A} (P : A -> Prop) n m (v : Vector.t A (n + m)) :
    ForallV P v -> ForallV P (fst (splitat _ v)).
  Proof.
    intro Hv.
    erewrite append_splitat in Hv by apply surjective_pairing.
    apply ForallV_append in Hv. tauto.
  Qed.

  Lemma ForallV_splitat2 {A} (P : A -> Prop) n m (v : Vector.t A (n + m)) :
    ForallV P v -> ForallV P (snd (splitat _ v)).
  Proof.
    intro Hv.
    erewrite append_splitat in Hv by apply surjective_pairing.
    apply ForallV_append in Hv. tauto.
  Qed.

  Lemma ForallV_to_list_iff {A} (P : A -> Prop) n (v : Vector.t A n) :
    ForallV P v <-> List.Forall P (to_list v).
  Proof.
    revert v; induction n; intro v; intros;
      [ eapply case0 with (v:=v) | rewrite (eta v) ].
    all:repeat match goal with
               | _ => progress cbn [ForallV]
               | _ => progress autorewrite with push_to_list vsimpl
               | H : _ /\ _ |- _ => destruct H
               | H : List.Forall _ (_ :: _)%list |- _ =>
                 inversion H; subst; clear H
               | |- _ <-> _ => split; intros; [ constructor | ]
               | |- _ /\ _ => split
               | _ => apply IHn; solve [auto]
               | _ => tauto
               end.
  Qed.
End ForallV.

Section AlgebraicFold.
  Local Notation t := Vector.t.

  Lemma fold_left_S_identity' {A} (f : A -> A -> A) id (valid : A -> Prop)
        (left_identity : forall a, valid a -> f id a = a) n (v : t A (S n)) :
    ForallV valid v ->
    Vector.fold_left f id v = Vector.fold_left f (Vector.hd v) (Vector.tl v).
  Proof.
    cbn [ForallV]; destruct 1. rewrite (eta v).
    autorewrite with push_vector_fold vsimpl.
    rewrite left_identity by auto. reflexivity.
  Qed.

  Lemma fold_left_S_identity {A} (f : A -> A -> A) id
        (left_identity : forall a, f id a = a) n (v : t A (S n)) :
    Vector.fold_left f id v = Vector.fold_left f (Vector.hd v) (Vector.tl v).
  Proof.
    eapply fold_left_S_identity' with (valid:=fun _ => True); auto; [ ].
    apply ForallV_trivial. tauto.
  Qed.

  Lemma fold_left_preserves_valid {A} (f : A -> A -> A) (valid : A -> Prop)
        (preserves_valid : forall a b, valid a -> valid b -> valid (f a b)) :
    forall n start (v : t A n),
      ForallV valid v -> valid start ->
      valid (Vector.fold_left f start v).
  Proof.
    intros. rewrite fold_left_to_list.
    eapply List.fold_left_invariant with (I:=valid); eauto; [ ].
    intros *. rewrite InV_to_list_iff. intros.
    match goal with H : ForallV _ _ |- _ =>
                    eapply ForallV_forall in H; [ | solve [eauto] ] end.
    eauto.
  Qed.

  Lemma fold_left_S_assoc' {A} (f : A -> A -> A) (valid : A -> Prop) id
        (identity_valid : valid id)
        (preserves_valid : forall a b, valid a -> valid b -> valid (f a b))
        (right_identity : forall a, valid a -> f a id = a)
        (left_identity : forall a, valid a -> f id a = a)
        (associative :
           forall a b c,
             valid a -> valid b -> valid c ->
             f a (f b c) = f (f a b) c) :
    forall n start (v : t A n),
      ForallV valid v -> valid start ->
      Vector.fold_left f start v = f start (Vector.fold_left f id v).
  Proof.
    induction n; intros; autorewrite with push_vector_fold.
    { rewrite right_identity by auto. reflexivity. }
    { match goal with H : ForallV _ _ |- _ => destruct H end.
      rewrite left_identity by eauto.
      erewrite <-fold_left_S_identity' by (cbn [ForallV]; eauto).
      rewrite IHn, <-associative; auto;
        [ | apply fold_left_preserves_valid with (valid0:=valid); solve [auto] ].
      rewrite fold_left_S with (b:=id).
      f_equal. rewrite !left_identity, <-IHn by auto.
      reflexivity. }
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
End AlgebraicFold.

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

  Fixpoint nth_default {n} (default: A) p (v: t A n): A :=
    match p with
    | 0 =>
        match v with
        | [] => default
        | x :: _ => x
        end
    | S p' =>
        match v with
        | [] => default
        | _ :: v' => nth_default default p' v'
        end
    end.

  Definition of_list_sized {A} (a : A) (n : nat) (l : list A) : Vector.t A n :=
    resize_default a  _ (Vector.of_list l).

  Lemma of_list_sized_to_list a n (v : t A n) :
    of_list_sized a n (to_list v) = v.
  Proof.
    cbv [of_list_sized].
    revert v; induction n; intros; [ apply nil_eq | ].
    rewrite (eta v). autorewrite with push_to_list.
    cbn [of_list length resize_default].
    autorewrite with vsimpl. rewrite IHn.
    reflexivity.
  Qed.

  Lemma to_list_of_list_sized a n (l : list A) :
    length l = n ->
    to_list (of_list_sized a n l) = l.
  Proof.
    cbv [of_list_sized]; intros; subst.
    rewrite resize_default_id, to_list_of_list_opp.
    reflexivity.
  Qed.

  Lemma of_list_sized_cons n (l : list A) a d :
    of_list_sized d (S n) (a :: l) = (a :: of_list_sized d n l)%vector.
  Proof. reflexivity. Qed.

  Lemma of_list_sized_0_nil (d : A) : of_list_sized d 0 [] = []%vector.
  Proof. reflexivity. Qed.

  Lemma eqb_fold A_beq n (v1 v2 : Vector.t A n) :
    Vector.eqb A A_beq v1 v2
    = Vector.fold_left andb true (Vector.map2 A_beq v1 v2).
  Proof.
    revert v1 v2; induction n.
    { intros v1 v2.
      eapply Vector.case0 with (v:=v1).
      eapply Vector.case0 with (v:=v2).
      reflexivity. }
    { intros v1 v2. rewrite (Vector.eta v1), (Vector.eta v2). cbn [Vector.eqb].
      autorewrite with push_vector_fold push_vector_map vsimpl.
      rewrite Bool.andb_true_l, IHn.
      symmetry; apply Vector.fold_left_S_assoc;
      auto using Bool.andb_true_r, Bool.andb_true_l, Bool.andb_assoc. }
  Qed.

  Lemma fold_andb_eq_iff A_beq n (v1 v2 : Vector.t A n) :
    (forall x y, A_beq x y = true <-> x = y) ->
    Vector.fold_left andb true (Vector.map2 A_beq v1 v2) = true <-> v1 = v2.
  Proof. intros. rewrite <-eqb_fold. apply Vector.eqb_eq; auto. Qed.

  Lemma fold_andb_neq_iff A_beq n (v1 v2 : Vector.t A n) :
    (forall x y, A_beq x y = true <-> x = y) ->
    Vector.fold_left andb true (Vector.map2 A_beq v1 v2) = false <-> v1 <> v2.
  Proof.
    intros; rewrite <-fold_andb_eq_iff by auto.
    erewrite Bool.not_true_iff_false. reflexivity.
  Qed.
End Vector.
Hint Rewrite @to_list_of_list_sized using solve [eauto] : push_to_list.
Hint Rewrite @of_list_sized_0_nil @of_list_sized_cons @of_list_sized_to_list
     using solve [eauto] : push_of_list_sized.

Section NthDefault.
  Lemma nth_default_snoc {A n} (v : Vector.t A n) x i d :
    i < n -> nth_default d i (snoc v x) = nth_default d i v.
  Proof.
    revert n v; induction i; intros.
    { destruct n; [ lia | ]. rewrite (eta v).
      reflexivity. }
    { destruct n; [ lia | ]. rewrite (eta v).
      cbn [snoc]. autorewrite with vsimpl.
      cbn [nth_default]. rewrite IHi by lia.
      reflexivity. }
  Qed.

  Lemma nth_default_to_list {A n} (v : Vector.t A n) d i :
    nth_default d i v = List.nth i (to_list v) d.
  Proof.
    revert n v; induction i; intros.
    { destruct n; [ eapply case0 with (v:=v) | rewrite (eta v) ];
        reflexivity. }
    { destruct n; [ eapply case0 with (v:=v); reflexivity | ].
      rewrite (eta v). autorewrite with push_to_list.
      cbn [nth_default List.nth]. apply IHi. }
  Qed.

  Lemma nth_default_resize_default {A n} (v : Vector.t A n) d m i :
    m = n -> nth_default d i (resize_default d m v) = nth_default d i v.
  Proof.
    intros; subst. rewrite resize_default_id. reflexivity.
  Qed.
End NthDefault.

(* Prove two vectors are equal by proving each element is equal *)
Ltac fequal_vector :=
  repeat match goal with
         | |- Vector.cons _ _ _ _ = Vector.cons _ _ _ _ => f_equal
         end.

(* Useful tactic to destruct vectors of constant length *)
Ltac constant_vector_simpl vec :=
  lazymatch type of vec with
  | Vector.t _ (S ?n) =>
    let v' := fresh "v" in
    let x := fresh "x" in
    rewrite (eta vec); set (v' := tl vec); set (x:=hd vec);
    cbv beta in v', x; constant_vector_simpl v'
  | Vector.t _ 0 => eapply case0 with (v := vec)
  end.
