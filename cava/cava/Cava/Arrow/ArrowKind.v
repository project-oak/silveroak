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

From Coq Require Import Lists.List NaryFunctions Arith NArith Vector Eqdep_dec.

Import ListNotations.
Import VectorNotations.

From Cava Require Import Types.

Inductive Kind : Set :=
| Tuple: Kind -> Kind -> Kind
| Unit: Kind
| Bit: Kind
| Vector: Kind -> nat -> Kind.

Fixpoint eq_kind_dec (k1 k2: Kind) {struct k1} : {k1=k2} + {k1<>k2}.
Proof.
  decide equality.
  exact (PeanoNat.Nat.eq_dec n n0).
Defined.

(* TODO: Coq.Init.Logic f_equal2 is opaque, f_equal is not, should transparency here be upstreamed? *)
Lemma f_equal2 {A B C} {x y:A}  {a b: B} (f: A -> B -> C) : x = y -> a = b -> f x a = f y b.
Proof.
  destruct 1.
  destruct 1.
  trivial.
Defined.

Definition kind_proj_tup_left (ty: Kind):=
  match ty with
  | Tuple t1 t2 => t1
  | _ => ty
  end.

Definition kind_proj_tup_right (ty: Kind):=
  match ty with
  | Tuple t1 t2 => t2
  | _ => ty
  end.
Definition kind_proj_vec_t (ty: Kind):=
  match ty with
  | Vector t _ => t
  | _ => ty
  end.
Definition kind_proj_vec_n (ty: Kind) :=
  match ty with
  | Vector _ n => n
  | _ => 0
  end.

Lemma UIP_refl_kind (ty:Kind) (x : ty = ty) : x = eq_refl.
Proof.
  induction ty.

  - specialize IHty1 with (f_equal kind_proj_tup_left x).
    specialize IHty2 with (f_equal kind_proj_tup_right x).
    change eq_refl with (f_equal2 Tuple (@eq_refl _ ty1) (@eq_refl _ ty2)).
    rewrite <- IHty1.
    rewrite <- IHty2.
    clear IHty1.
    clear IHty2.

    change (match Tuple ty1 ty2 as x return Tuple ty1 ty2 = x -> Prop with
            | Tuple _ _ =>
              fun H => H = f_equal2 Tuple (f_equal kind_proj_tup_left H) (f_equal kind_proj_tup_right H)
            | _ => fun _ => True
            end x).
    pattern (Tuple ty1 ty2) at 2 3, x.
    destruct x.
    reflexivity.

  - change (match Unit as n return Unit=n -> Prop with
            | Unit => fun x => x = eq_refl
            | _ => fun _ => True
            end x); destruct x; reflexivity.

  - change (match Bit as n return Bit=n -> Prop with
            | Bit => fun x => x = eq_refl
            | _ => fun _ => True
            end x); destruct x; reflexivity.

  - specialize IHty with (f_equal kind_proj_vec_t x).
    pose proof (UIP_refl_nat n (f_equal kind_proj_vec_n x)).
    change eq_refl with (f_equal2 Vector (@eq_refl _ ty) (@eq_refl _ n)).
    rewrite <- IHty.
    rewrite <- H.
    clear IHty.
    clear H.
    change (match Vector ty n as a return Vector ty n = a -> Prop with
            | Vector _ _ => fun x => x = f_equal2 Vector (f_equal kind_proj_vec_t x) (f_equal kind_proj_vec_n x)
            | _ => fun _ => True
            end x).

    pattern (Vector ty n) at 2 3, x.
    destruct x.
    reflexivity.
Defined.


Lemma kind_eq: forall ty, eq_kind_dec ty ty = left eq_refl.
Proof.
  intros.
  destruct (eq_kind_dec ty ty); try rewrite (UIP_refl_kind _ _); auto.
  destruct n.
  reflexivity.
Qed.

Ltac reduce_kind_eq :=
  match goal with
  | [ |- context[eq_kind_dec _ _] ] =>
    rewrite kind_eq; unfold eq_rect_r, eq_rect, eq_sym
  | [H: context[eq_kind_dec _ _] |- _] =>
    rewrite kind_eq in H; unfold eq_rect_r, eq_rect, eq_sym in H
  end; try subst.

Declare Scope kind_scope.
Bind Scope kind_scope with Kind.

Notation "<< x >>" := (x) : kind_scope.
Notation "<< x , .. , y , z >>" := (Tuple x .. (Tuple y z )  .. ) : kind_scope.

Fixpoint arg_length (ty: Kind) :=
match ty with
| Tuple _ r => S (arg_length r)
| _ => O
end.

Definition arg_length_order (ty1 ty2: Kind) :=
  arg_length ty1 < arg_length ty2.

Lemma arg_length_order_wf': forall len ty, arg_length ty < len -> Acc arg_length_order ty.
Proof.
  unfold arg_length_order; induction len; intros.
  - inversion H.
  - refine (Acc_intro _ _); intros.
    eapply (IHlen y).

    apply lt_n_Sm_le in H.
    apply (lt_le_trans _ _ _ H0 H).
Defined.

Lemma arg_length_order_wf: well_founded arg_length_order.
Proof.
  cbv [well_founded]; intros.
  eapply arg_length_order_wf'.
  eauto.
Defined.

Fixpoint vec_to_nprod (A: Type) n (v: Vector.t A n): A^n :=
  match v with
  | [] => tt
  | x::xs => (x, vec_to_nprod A _ xs)
  end%vector.

Fixpoint insert_rightmost_unit (ty: Kind): Kind :=
match ty with
| Tuple l r => Tuple l (insert_rightmost_unit r)
| Unit => Unit
| x => Tuple x Unit
end.

Fixpoint remove_rightmost_unit (ty: Kind): Kind :=
match ty with
| Tuple l Unit => l
| Tuple l r => Tuple l (remove_rightmost_unit r)
| x => x
end.
