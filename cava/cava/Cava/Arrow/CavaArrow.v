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

From Arrow Require Import Category Arrow.
From Coq Require Import Lists.List NaryFunctions String Arith NArith VectorDef Lia.

Import ListNotations.
Import VectorNotations.

From Cava Require Import Types.

Local Open Scope category_scope.
Local Open Scope arrow_scope.

(* Class CircuitLaws `(A: Arrow, ! ArrowCopy A, ! ArrowSwap A, ! ArrowDrop A) := {
  cancelr_unit_uncancelr {x}: @cancelr x >>> uncancelr =M= id;
  cancell_unit_uncancell {x}: @cancell _ _ A x >>> uncancell =M= id;
  uncancelr_cancelr {x}:      @uncancelr _ _ A x >>> cancelr =M= id;
  uncancell_cancell {x}:      @uncancell _ _ A x >>> cancell =M= id;

  drop_annhilates {x y} (f: x~>y): f >>> drop =M= drop;

  cancelr_unit_is_drop : @cancelr A unit =M= drop;
  cancell_unit_is_drop : @cancell A unit =M= drop;

  first_first   {x y z w} (f: x~>y) (g:y~>z): @first A x y w f >>> first g  =M= first (f >>> g);
  second_second {x y z w} (f: x~>y) (g:y~>z): @second A x y w f >>> second g  =M= second (f >>> g);

  swap_swap {x y}: @swap A _ x y >>> swap =M= id;

  first_id  {x w}: @first A x x w id  =M= id;
  second_id {x w}: @second A x x w id  =M= id;

  first_f  {x y w} (f: x~>y) (g:x~>y): f =M= g -> @first A x y w f =M= first g;
  second_f {x y w} (f: x~>y) (g:x~>y): f =M= g -> @second A x y w f =M= second g;
}. *)

Inductive Kind : Set :=
| Tuple: Kind -> Kind -> Kind
| Unit: Kind
| Bit: Kind
| Vector: Kind -> nat -> Kind.

Fixpoint decKind (k1 k2: Kind) {struct k1} : {k1=k2} + {k1<>k2}. 
Proof.
  decide equality.
  exact (PeanoNat.Nat.eq_dec n n0).
Defined.

Require Import Eqdep.

Lemma kind_eq: forall ty, decKind ty ty = left eq_refl.
Proof.
  intros. 
  destruct (decKind ty ty); try rewrite (UIP_refl _ _ _); auto.
  destruct n.
  reflexivity.
Qed.

Ltac reduce_kind_eq :=
  match goal with 
  | [ |- context[decKind _ _] ] =>
    rewrite kind_eq; unfold eq_rect_r, eq_rect, eq_sym
  | [H: context[decKind _ _] |- _] =>
    rewrite kind_eq in H; unfold eq_rect_r, eq_rect, eq_sym in H
  end; try subst.

Declare Scope kind_scope.
Bind Scope kind_scope with Kind.
Delimit Scope kind_scope with Kind.
Delimit Scope kind_scope with Category.

Notation "<< x >>" := (x) : kind_scope.
Notation "<< x , .. , y , z >>" := (Tuple x .. (Tuple y z )  .. ) : kind_scope.

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

Fixpoint arg_length (ty: Kind) :=
match ty with
| Tuple _ r => 1 + (arg_length r)
| _ => 0
end.

Definition arg_length_order (ty1 ty2: Kind) :=
  arg_length ty1 < arg_length ty2.

Lemma arg_length_order_wf': forall len ty, arg_length ty < len -> Acc arg_length_order ty.
Proof.
  unfold arg_length_order; induction len; intros.
  - inversion H.
  - refine (Acc_intro _ _); intros.
    eapply (IHlen y).
    lia.
Defined.

Lemma arg_length_order_wf: well_founded arg_length_order.
Proof.
  cbv [well_founded]; intros.
  eapply arg_length_order_wf'.
  eauto.
Defined.

(* Cava *)
Class Cava := {
  cava_cat :> Category Kind;
  cava_arrow :> Arrow Kind cava_cat Unit Tuple;
  cava_arrow_stkc :> ArrowSTKC cava_arrow;
  cava_arrow_loop :> ArrowLoop cava_arrow;

  vec_index n := Vector Bit (Nat.log2_up n);

  constant : bool -> (Unit ~> Bit);
  constant_bitvec n: N -> (Unit ~> Vector Bit n);

  mk_module i o: string -> (i~>o) -> (i~>o);

  not_gate:  Bit        ~> Bit;
  and_gate:  Bit ** Bit ~> Bit;
  nand_gate: Bit ** Bit ~> Bit;
  or_gate:   Bit ** Bit ~> Bit;
  nor_gate:  Bit ** Bit ~> Bit;
  xor_gate:  Bit ** Bit ~> Bit;
  xnor_gate: Bit ** Bit ~> Bit;
  buf_gate:  Bit        ~> Bit;

  delay_gate {o} : o ~> o;

  xorcy:     Bit ** Bit ~> Bit;
  muxcy:     Bit ** (Bit ** Bit) ~> Bit;
  
  unsigned_add a b c: Vector Bit a ** Vector Bit b ~> Vector Bit c;

  lut n: (bool^^n --> bool) -> Vector Bit n ~> Bit;

  empty_vec o: u ~> Vector o 0;
  index n o: Vector o n ** vec_index n ~> o;
  cons n o: o ** Vector o n ~> Vector o (S n);
  snoc n o: Vector o n ** o ~> Vector o (S n);
  uncons n o: Vector o (S n) ~> o ** Vector o n;
  unsnoc n o: Vector o (S n) ~> Vector o n ** o;
  concat n m o: Vector o n ** Vector o m ~> Vector o (n + m);
  split n m o: m <= n -> Vector o n ~> (Vector o m ** Vector o (n - m));
  (* slice n x y where x >= y, x is inclusive 
  So, somevec[1:0] is the vector [vec[0],vec[1]] : Vector 2 _ *)
  slice n x y o: x < n -> y <= x -> Vector o n ~> Vector o (x - y + 1);
}.

Coercion cava_cat: Cava >-> Category.
Coercion cava_arrow: Cava >-> Arrow.
Coercion cava_arrow_stkc: Cava >-> ArrowSTKC.
Coercion cava_arrow_loop: Cava >-> ArrowLoop.

Declare Scope cava_scope.
Bind Scope cava_scope with Cava.
Delimit Scope cava_scope with cava.

Open Scope cava_scope.

Definition high {_: Cava}: Unit ~> Bit := constant true.
Definition low {_: Cava}: Unit ~> Bit := constant false.

Fixpoint insert_rightmost_tt `{Cava} (ty: Kind): ty ~> (insert_rightmost_unit ty).
Proof.
  intros.
  destruct ty.
  exact (second (insert_rightmost_tt _ ty2)).
  exact id.
  exact uncancelr.
  exact uncancelr.
Defined.

Fixpoint insert_rightmost_tt1 `{Cava} (ty: Kind): (remove_rightmost_unit ty) ~> ty.
Proof.
  refine (
  Fix arg_length_order_wf (fun ty => (remove_rightmost_unit ty) ~> ty )
    (fun (ty:Kind)
      (insert_rightmost_tt1': forall ty', arg_length_order ty' ty -> (remove_rightmost_unit ty') ~> ty') =>
        match ty as sty return ty=sty -> (remove_rightmost_unit sty) ~> sty with
        | Tuple _ Unit => fun _ => uncancelr
        | Tuple l ty2 => fun H => (@second _ _ _ _ _ _ _ l (insert_rightmost_tt1' ty2 _ ))
        | _ => fun _ => id
        end eq_refl
        ) ty);
  rewrite H;
  cbv [arg_length_order ty2];
  auto.
Defined.

Fixpoint remove_rightmost_tt `{Cava} (ty: Kind): ty ~> (remove_rightmost_unit ty).
  refine (Fix arg_length_order_wf (fun ty => ty ~> (remove_rightmost_unit ty))
    (fun (ty:Kind)
      (remove_rightmost_tt': forall ty', arg_length_order ty' ty -> ty' ~> (remove_rightmost_unit ty')) =>
        match ty as sty return ty=sty -> sty ~> (remove_rightmost_unit sty) with
        | Tuple _ Unit => fun _ => cancelr
        | Tuple l ty2 => fun H => (@second _ _ _ _ _ _ _ l (remove_rightmost_tt' ty2 _ ))
        | _ => fun _ => id
        end eq_refl
        ) ty);
  rewrite H;
  cbv [arg_length_order ty2];
  auto.
Defined.