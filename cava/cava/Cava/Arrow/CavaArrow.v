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

From Arrow Require Import Category Arrow Kappa ClosureConversion.
From Coq Require Import Lists.List NaryFunctions String Arith NArith VectorDef Lia.

Import ListNotations.
Import VectorNotations.

From Cava Require Import Types Arrow.ArrowKind.
From Cava Require Export Arrow.ArrowKind.

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

(* Cava *)
Notation "[ x ~~> .. ~~> y ~~> z ]" := (morphism (Tuple x .. (Tuple y Unit) ..) z) : arrow_scope.
Class Cava := {
  cava_cat :> Category Kind;
  cava_arrow :> Arrow Kind cava_cat Unit Tuple;
  cava_arrow_stkc :> ArrowSTKC cava_arrow;
  cava_arrow_loop :> ArrowLoop cava_arrow;

  vec_index n := Vector Bit (Nat.log2_up n);

  constant : bool -> (Unit ~> Bit);
  constant_bitvec n: N -> (Unit ~> Vector Bit n);

  mk_module i o: string -> (i~>o) -> (i~>o);

  not_gate:  [ Bit ~~> Bit ];
  and_gate:  [ Bit ~~> Bit ~~> Bit];
  nand_gate: [ Bit ~~> Bit ~~> Bit];
  or_gate:   [ Bit ~~> Bit ~~> Bit];
  nor_gate:  [ Bit ~~> Bit ~~> Bit];
  xor_gate:  [ Bit ~~> Bit ~~> Bit];
  xnor_gate: [ Bit ~~> Bit ~~> Bit];
  buf_gate:  [ Bit         ~~> Bit];

  delay_gate {o} : [ o ~~> o ];

  xorcy:     [ Bit ~~> Bit ~~> Bit ];
  muxcy:     [ Bit ~~> (Bit ** Bit) ~~> Bit ];
  
  unsigned_add a b c: [ Vector Bit a ~~> Vector Bit b ~~> Vector Bit c ];
  unsigned_sub a: [ Vector Bit a ~~> Vector Bit a ~~> Vector Bit a ];

  lut n: (bool^^n --> bool) -> [Vector Bit n ~~> Bit];

  empty_vec o: u ~> Vector o 0;
  index n o: [Vector o n ~~> vec_index n ~~> o];
  cons n o: [o ~~> Vector o n ~~> Vector o (S n)];
  snoc n o: [Vector o n ~~> o ~~> Vector o (S n)];
  uncons n o: [Vector o (S n) ~~> o ** Vector o n];
  unsnoc n o: [Vector o (S n) ~~> Vector o n ** o];
  concat n m o: [Vector o n ~~> Vector o m ~~> Vector o (n + m)];
  split n m o: [Vector o (n+m) ~~> Vector o n ** Vector o m];
  (* slice n x y where x >= y, x is inclusive 
  So, somevec[1:0] is the vector [vec[0],vec[1]] : Vector 2 _ *)
  slice n x y o: x < n -> y <= x -> [Vector o n ~~> Vector o (x - y + 1)];
}.

Coercion cava_cat: Cava >-> Category.
Coercion cava_arrow: Cava >-> Arrow.
Coercion cava_arrow_stkc: Cava >-> ArrowSTKC.
Coercion cava_arrow_loop: Cava >-> ArrowLoop.

Declare Scope cava_scope.
Bind Scope cava_scope with Cava.
Delimit Scope cava_scope with cava.

Open Scope cava_scope.

Ltac match_primitive X :=
  match X with 
  | (Category.id) => idtac

  | (first _) => idtac
  | (second _) => idtac
  | (cancelr) => idtac
  | (cancell) => idtac
  | (uncancelr) => idtac
  | (uncancell) => idtac
  | (assoc) => idtac
  | (unassoc) => idtac

  | (CavaArrow.constant _) => idtac
  | (CavaArrow.constant_bitvec _ _) => idtac
  | (CavaArrow.mk_module _ _) => idtac

  | (CavaArrow.not_gate) => idtac
  | (CavaArrow.and_gate) => idtac
  | (CavaArrow.nand_gate) => idtac
  | (CavaArrow.or_gate) => idtac
  | (CavaArrow.nor_gate) => idtac
  | (CavaArrow.xor_gate) => idtac
  | (CavaArrow.xnor_gate) => idtac
  | (CavaArrow.buf_gate) => idtac

  | (CavaArrow.delay_gate _) => idtac

  | (CavaArrow.xorcy) => idtac
  | (CavaArrow.muxcy) => idtac

  | (CavaArrow.unsigned_add _ _ _) => idtac

  | (CavaArrow.lut _) => idtac

  | (CavaArrow.empty_vec _) => idtac
  | (CavaArrow.index _ _) => idtac

  | (CavaArrow.cons _ _) => idtac
  | (CavaArrow.snoc _ _) => idtac
  | (CavaArrow.uncons _ _) => idtac
  | (CavaArrow.unsnoc _ _) => idtac
  | (CavaArrow.concat _ _ _) => idtac
  | (CavaArrow.split _ _ _ _) => idtac
  | (CavaArrow.slice _ _ _ _ _ _) => idtac
  end.

Ltac match_compose X :=
  match X with 
  | (Category.compose ?Y ?Z) =>
    (match_primitive Y + match_compose Y); 
    (match_primitive Z + match_compose Z)
  end.

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