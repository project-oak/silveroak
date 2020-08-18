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

Local Notation "[ x ~~~> .. ~~~> y ]" := (Tuple x .. (Tuple y Unit) ..).

Notation vec_index n := (Vector Bit (Nat.log2_up n)).

Inductive CircuitPrimitive :=
  | constant (b: bool)
  | constant_bitvec (n: nat) (v: N)
  | delay_gate (o: Kind)
  | not_gate 
  | buf_gate
  | uncons (n: nat) (o: Kind)
  | unsnoc (n: nat) (o: Kind)
  | slice (n: nat) (x y: nat) (o: Kind) 
  | split (n m: nat) (o: Kind) 
  | empty_vec (o: Kind)
  | lut (n: nat) (f: bool^^n --> bool)

  | and_gate  
  | nand_gate 
  | or_gate   
  | nor_gate
  | xor_gate
  | xnor_gate 
  | xorcy

  | muxcy
  | unsigned_add (a b c: nat)
  | unsigned_sub (a: nat)
  | index (n: nat) (o: Kind)
  | cons (n: nat) (o: Kind)
  | snoc (n: nat) (o: Kind)
  | concat (n m: nat) (o: Kind).

Fixpoint primitive_input (op: CircuitPrimitive): Kind :=
  match op with
  | constant v => Unit
  | constant_bitvec n v => Unit
  | delay_gate o => Tuple o Unit
  | not_gate => Tuple Bit Unit
  | buf_gate => Tuple Bit Unit
  | uncons n o => Tuple (Vector o (S n)) Unit
  | unsnoc n o => Tuple (Vector o (S n)) Unit
  | slice n x y o => Tuple (Vector o n) Unit
  | split n m o => Tuple (Vector o (n+m)) Unit
  | empty_vec o => Unit
  | lut n f => Tuple (Vector Bit n) Unit 

  | muxcy => [ Bit ~~~> Tuple Bit Bit ]
  | unsigned_add a b c => [ Vector Bit a ~~~> Vector Bit b ]
  | unsigned_sub a => [ Vector Bit a ~~~> Vector Bit a ]
  | index n o => [ Vector o n ~~~> vec_index n ]
  | cons n o => [ o ~~~> Vector o n ]
  | snoc n o => [ Vector o n ~~~> o ]
  | concat n m o => [ Vector o n ~~~> Vector o m ]

  | _ => [ Bit ~~~> Bit ]
  end.

Fixpoint primitive_output (op: CircuitPrimitive): Kind :=
  match op with
  | constant v => Bit
  | constant_bitvec n v => Vector Bit n
  | delay_gate o => o
  | not_gate => Bit
  | buf_gate => Bit
  | uncons n o => Tuple o (Vector o n)
  | unsnoc n o => Tuple (Vector o n) o
  | slice n x y o => Vector o (x - y + 1)
  | split n m o => Tuple (Vector o n) (Vector o m)
  | empty_vec o => Vector o 0
  | lut n f => Bit

  | muxcy => Bit
  | unsigned_add a b c => Vector Bit c 
  | unsigned_sub a => Vector Bit a
  | index n o => o
  | cons n o => Vector o (S n)
  | snoc n o => Vector o (S n)
  | concat n m o => Vector o (n + m)

  | _ => Bit
  end.

Notation arrow_input x := (arrow_input (object:=Kind) (unit:=Unit) (product:=Tuple) x).
Notation arrow_output x := (arrow_output (object:=Kind) (unit:=Unit) (product:=Tuple) x).

(* Single clock circuit *)
Inductive Circuit: Kind -> Kind -> Type := 
  | Structural: forall (x: ArrowStructure), Circuit (arrow_input x) (arrow_output x)
  | Primitive: forall (x: CircuitPrimitive), Circuit (primitive_input x) (primitive_output x)

  (* contains subcircuits *)
  | Composition: forall x y z, Circuit x y -> Circuit y z -> Circuit x z
  | First: forall x y z, Circuit x y -> Circuit (Tuple x z) (Tuple y z)
  | Second: forall x y z, Circuit x y -> Circuit (Tuple z x) (Tuple z y)
  | Loopr: forall x y z, Circuit (Tuple x z) (Tuple y z) -> Circuit x y
  | Loopl: forall x y z, Circuit (Tuple z x) (Tuple z y) -> Circuit x y
  .

(* Notation "[ x ~~> .. ~~> y ~~> z ]" := (morphism (Tuple x .. (Tuple y Unit) ..) z) : arrow_scope. *)
Notation "[ x ~~> .. ~~> y ~~> z ]" := (Circuit (Tuple x .. (Tuple y Unit) ..) z) : arrow_scope.

Instance CircuitCat : Category Kind := {
  morphism X Y := Circuit X Y;
  id X := Structural (Id X);
  compose X Y Z f g := Composition X Y Z g f;
}.

Instance CircuitArrow : Arrow Kind CircuitCat Unit Tuple := {
  first  f := First f;
  second f := Second f;
  assoc   x y z := Structural (Assoc x y z);
  unassoc x y z := Structural (Unassoc x y z);
  cancelr  x := Structural (Cancelr x);
  cancell  x := Structural (Cancell x);
  uncancell x := Structural (Uncancell x);
  uncancelr x := Structural (Uncancelr x);
}.

Instance CircuitArrowDrop : ArrowDrop CircuitArrow := { drop _ := Structural (Drop _); }.
Instance CircuitArrowSwap : ArrowSwap CircuitArrow := { swap _ _ := Structural (Swap _ _); }.
Instance CircuitArrowCopy : ArrowCopy CircuitArrow := { copy _ := Structural (Copy _); }.
Instance CircuitArrowLoop : ArrowLoop CircuitArrow := { loopl := Loopl; loopr := Loopr; }.
Instance CircuitArrowSTKC : ArrowSTKC CircuitArrow := { }.

Ltac match_primitive X :=
  match X with 
  | (Circuit _ _ _) => idtac
  end.

Ltac match_compose X :=
  match X with 
  | (Composition _ _ ?Y ?Z) => idtac
  end.

Definition high : Unit ~> Bit := Primitive (constant true).
Definition low : Unit ~> Bit := Primitive (constant false).

Fixpoint insert_rightmost_tt (ty: Kind): ty ~> (insert_rightmost_unit ty).
Proof.
  intros.
  destruct ty.
  exact (second (insert_rightmost_tt ty2)).
  exact id.
  exact uncancelr.
  exact uncancelr.
Defined.

Fixpoint insert_rightmost_tt1 (ty: Kind): (remove_rightmost_unit ty) ~> ty.
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

Fixpoint remove_rightmost_tt (ty: Kind): ty ~> (remove_rightmost_unit ty).
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