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

From Coq Require Import Numbers.NaryFunctions Arith.Arith NArith.NArith.
From Coq Require Import Vectors.Vector.
From Coq Require Import Bool.Bool.
From Coq Require Import ZArith.ZArith.
From Cava Require Import VectorUtils.
From Cava Require Import BitArithmetic.

Import VectorNotations.

(* Module PrimitiveNotations. *)

From Cava Require Export Arrow.ArrowKind.

Notation vec_index n := (Vector Bit (Nat.log2_up n)).

Inductive NullaryPrimitive : Kind -> Type :=
| Constant ty (v: denote_kind ty):             NullaryPrimitive ty
| ConstantVec n ty (v: list (denote_kind ty)): NullaryPrimitive (Vector ty n)
| EmptyVec ty:                                 NullaryPrimitive (Vector ty 0).

Inductive UnaryPrimitive : Kind -> Kind -> Type:=
| BufGate:                              UnaryPrimitive Bit Bit
| Lut (n: nat) (f: bool^^n --> bool):   UnaryPrimitive <<Vector Bit n>> Bit
| Not:                                  UnaryPrimitive <<Bit>> Bit
| Fst (x y: Kind):                      UnaryPrimitive <<x, y>> x
| Snd (x y: Kind):                      UnaryPrimitive <<x, y>> y
| Uncons (n: nat) (ty: Kind):           UnaryPrimitive <<Vector ty (S n)>> <<ty, Vector ty n>>
| Unsnoc (n: nat) (ty: Kind):           UnaryPrimitive <<Vector ty (S n)>> <<Vector ty n, ty>>
| Slice (n: nat) (x y: nat) (ty: Kind): UnaryPrimitive <<Vector ty n>> <<Vector ty (x - y + 1)>>
| Split (n m: nat) (ty: Kind):          UnaryPrimitive <<Vector ty (n+m)>> <<Vector ty n, Vector ty m>>
.

Inductive BinaryPrimitive : Kind -> Kind -> Kind -> Type :=
| And:                          BinaryPrimitive << Bit >> << Bit >> << Bit >>
| Nand:                         BinaryPrimitive << Bit >> << Bit >> << Bit >>
| Or:                           BinaryPrimitive << Bit >> << Bit >> << Bit >>
| Nor:                          BinaryPrimitive << Bit >> << Bit >> << Bit >>
| Xor:                          BinaryPrimitive << Bit >> << Bit >> << Bit >>
| Xnor:                         BinaryPrimitive << Bit >> << Bit >> << Bit >>
| Xorcy:                        BinaryPrimitive << Bit >> << Bit >> << Bit >>
| Muxcy:                        BinaryPrimitive << Bit >> << Bit, Bit >> << Bit >>
| Pair (x y: Kind):             BinaryPrimitive << x >> << y >> << x, y >>
| UnsignedAdd (a b c: nat):     BinaryPrimitive << Vector Bit a >> << Vector Bit b >> << Vector Bit c >>
| UnsignedSub (a: nat):         BinaryPrimitive << Vector Bit a >> << Vector Bit a >> << Vector Bit a >>
| Index (n: nat) (ty: Kind):    BinaryPrimitive << Vector ty n >> << vec_index n >> << ty >>
| Cons (n: nat) (ty: Kind):     BinaryPrimitive << ty >> << Vector ty n >> << Vector ty (S n) >>
| Snoc (n: nat) (ty: Kind):     BinaryPrimitive << Vector ty n >> << ty >> << Vector ty (S n) >>
| Concat (n m: nat) (ty: Kind): BinaryPrimitive << Vector ty n >> << Vector ty m >> << Vector ty (n + m) >>
.

Inductive CircuitPrimitive :=
| P0 : forall x, NullaryPrimitive x -> CircuitPrimitive
| P1 : forall x y, UnaryPrimitive x y -> CircuitPrimitive
| P2 : forall x y z, BinaryPrimitive x y z -> CircuitPrimitive.

Definition primitive_input (p: CircuitPrimitive): Kind :=
  match p with
  | P0 _ _ => Unit
  | P1 x _ _ => x
  | P2 x y _ _ => Tuple x y
  end.

Definition primitive_output (p: CircuitPrimitive): Kind :=
  match p with
  | P0 x _ => x
  | P1 _ x _ => x
  | P2 _ _ x _ => x
  end.

Arguments P0 {_}.
Arguments P1 {_ _}.
Arguments P2 {_ _ _}.

Definition nullary_semantics ty (p: NullaryPrimitive ty): denote_kind ty :=
  match p with
  | Constant ty val => val
  | ConstantVec n ty val => resize_default (kind_default _) n (Vector.of_list val)
  | EmptyVec o => []
  end.

Definition unary_semantics x y (p: UnaryPrimitive x y)
  : denote_kind x -> denote_kind y :=
  match p with
  | Not => fun b => negb b
  | BufGate => fun b => b
  | Uncons n o => fun v => (hd v, tl v)
  | Unsnoc n o => fun v => unsnoc v
  | Split n m o => fun v => (Vector.splitat n v)
  | Slice n x y o => fun v => slice_by_position n x y (kind_default _) v
  | Lut n f => fun x =>
    let f' := NaryFunctions.nuncurry bool bool n f in
    (f' (vec_to_nprod _ _ x))
  | Fst _ _ => fun x => fst x
  | Snd _ _ => fun x => snd x
  end.

Definition binary_semantics x y z (p: BinaryPrimitive x y z)
  : denote_kind x -> denote_kind y -> denote_kind z :=
  match p with
  | And => fun x y => x && y
  | Nand => fun x y => negb ( x && y)
  | Or => fun x y => orb x y
  | Nor => fun x y => negb (orb x y)
  | Xor => fun x y => xorb x y
  | Xnor => fun x y => negb (xorb x y)
  | Xorcy => fun x y => xorb x y

  | Pair _ _ => fun x y => (x,y)

  | Muxcy => fun x y => (if x then fst y else snd y)
  | UnsignedAdd m n s => fun av bv =>
    let a := Ndigits.Bv2N av in
    let b := Ndigits.Bv2N bv in
    let c := (a + b)%N in
    (Ndigits.N2Bv_sized s c)
  | UnsignedSub s => fun av bv =>
    let a := Z.of_N (Ndigits.Bv2N av) in
    let b := Z.of_N (Ndigits.Bv2N bv) in
    let mod_const := (2^(Z.of_nat s))%Z in
    let c := ((a - b + mod_const) mod mod_const)%Z in
    (Ndigits.N2Bv_sized s (Z.to_N c))
  | Index n o => fun x y =>
    nth_default (kind_default _) (bitvec_to_nat y) x
  | Cons n o => fun x v => (x :: v)
  | Snoc n o => fun v x => snoc v x
  | Concat n m o => fun x y => Vector.append x y
  end.

Definition primitive_semantics (p: CircuitPrimitive):
  denote_kind (primitive_input p) -> denote_kind (primitive_output p) :=
  match p with
  | P0 p => fun _ => nullary_semantics _ p
  | P1 p => fun x => unary_semantics _ _ p x
  | P2 p => fun '(x, y) => binary_semantics _ _ _ p x y
  end.

