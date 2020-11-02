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

From Coq Require Import NaryFunctions Arith NArith.
From Coq Require Import Vectors.Vector.
From Coq Require Import Bool.Bool.
From Coq Require Import ZArith.
From Cava Require Import VectorUtils.
From Cava Require Import BitArithmetic.

Import VectorNotations.

From Cava Require Export Arrow.ArrowKind.

Local Notation "[ x ~~~> .. ~~~> y ]" := (Tuple x .. (Tuple y Unit) ..).

Notation vec_index n := (Vector Bit (Nat.log2_up n)).

(* TODO(blaxill): split type into e.g. unary binary etc ops? *)
Inductive CircuitPrimitive :=
  | Constant (ty: Kind) (v: denote_kind ty)
  | ConstantVec (n:nat) (ty: Kind) (v: list (denote_kind ty))
  | Delay (o: Kind)
  | BufGate

  | Lut (n: nat) (f: bool^^n --> bool)

  | Not
  | And
  | Nand
  | Or
  | Nor
  | Xor
  | Xnor
  | Xorcy
  | Muxcy

  | Fst (x y: Kind)
  | Snd (x y: Kind)
  | Pair (x y: Kind)

  | UnsignedAdd (a b c: nat)
  | UnsignedSub (a: nat)

  | Index (n: nat) (o: Kind)
  | Cons (n: nat) (o: Kind)
  | Snoc (n: nat) (o: Kind)
  | Concat (n m: nat) (o: Kind)
  | Uncons (n: nat) (o: Kind)
  | Unsnoc (n: nat) (o: Kind)
  | Slice (n: nat) (x y: nat) (o: Kind)
  | Split (n m: nat) (o: Kind)
  | EmptyVec (o: Kind)
.

Definition primitive_input (op: CircuitPrimitive): Kind :=
  match op with
  | Constant _ _ => Unit
  | ConstantVec _ _ _ => Unit
  | Delay o => Tuple o Unit
  | Not => Tuple Bit Unit
  | BufGate => Tuple Bit Unit
  | Uncons n o => Tuple (Vector o (S n)) Unit
  | Unsnoc n o => Tuple (Vector o (S n)) Unit
  | Slice n x y o => Tuple (Vector o n) Unit
  | Split n m o => Tuple (Vector o (n+m)) Unit
  | EmptyVec o => Unit
  | Lut n f => Tuple (Vector Bit n) Unit

  | Muxcy => [ Bit ~~~> Tuple Bit Bit ]
  | UnsignedAdd a b c => [ Vector Bit a ~~~> Vector Bit b ]
  | UnsignedSub a => [ Vector Bit a ~~~> Vector Bit a ]
  | Index n o => [ Vector o n ~~~> vec_index n ]
  | Cons n o => [ o ~~~> Vector o n ]
  | Snoc n o => [ Vector o n ~~~> o ]
  | Concat n m o => [ Vector o n ~~~> Vector o m ]

  | Fst x y => Tuple (Tuple x y) Unit
  | Snd x y => Tuple (Tuple x y) Unit
  | Pair x y => [ x ~~~> y ]

  | _ => [ Bit ~~~> Bit ]
  end.

Definition primitive_output (op: CircuitPrimitive): Kind :=
  match op with
  | Constant ty _ => ty
  | ConstantVec n ty _ => Vector ty n
  | Delay o => o
  | Not => Bit
  | BufGate => Bit
  | Uncons n o => Tuple o (Vector o n)
  | Unsnoc n o => Tuple (Vector o n) o
  | Slice n x y o => Vector o (x - y + 1)
  | Split n m o => Tuple (Vector o n) (Vector o m)
  | EmptyVec o => Vector o 0
  | Lut n f => Bit

  | Muxcy => Bit
  | UnsignedAdd a b c => Vector Bit c
  | UnsignedSub a => Vector Bit a
  | Index n o => o
  | Cons n o => Vector o (S n)
  | Snoc n o => Vector o (S n)
  | Concat n m o => Vector o (n + m)

  | Fst x _ => x
  | Snd _ y => y
  | Pair x y => Tuple x y

  | _ => Bit
  end.

Definition primitive_interp p: denote_kind (primitive_input p) -> denote_kind (primitive_output p) :=
    match p as p return denote_kind (primitive_input p) -> denote_kind (primitive_output p) with
    | Constant ty val => fun _ => val
    | ConstantVec n ty val => fun _ => resize_default (kind_default _) n (Vector.of_list val)
    | Delay o => fun _ => kind_default _
    | Not => fun b => negb (fst b)
    | BufGate => fun b => fst b
    | Uncons n o => fun v => (hd (fst v), tl (fst v))
    | Unsnoc n o => fun v => unsnoc (fst v)
    | Split n m o => fun v => (Vector.splitat n (fst v))
    | Slice n x y o => fun v => slice_by_position n x y (kind_default _) (fst v)
    | EmptyVec o => fun _ => []
    | Lut n f => fun '(i,_) =>
      let f' := NaryFunctions.nuncurry bool bool n f in
      (f' (vec_to_nprod _ _ i))

    | And => fun '(x,(y,_)) => x && y
    | Nand => fun '(x,(y,_)) => negb ( x && y)
    | Or => fun '(x,(y,_)) => orb x y
    | Nor => fun '(x,(y,_)) => negb (orb x y)
    | Xor => fun '(x,(y,_)) => xorb x y
    | Xnor => fun '(x,(y,_)) => negb (xorb x y)
    | Xorcy => fun '(x,(y,_)) => xorb x y

    | Fst _ _ => fun '((x,y),_) => x
    | Snd _ _ => fun '((x,y),_) => y
    | Pair _ _ => fun '(x,(y,_)) => (x,y)

    | Muxcy => fun i => (if fst i then fst (fst (snd i)) else snd (fst (snd i)))
    | UnsignedAdd m n s => fun '(av,(bv,_)) =>
      let a := Ndigits.Bv2N av in
      let b := Ndigits.Bv2N bv in
      let c := (a + b)%N in
      (Ndigits.N2Bv_sized s c)
    | UnsignedSub s => fun '(av, (bv, _)) =>
      let a := Z.of_N (Ndigits.Bv2N av) in
      let b := Z.of_N (Ndigits.Bv2N bv) in
      let mod_const := (2^(Z.of_nat s))%Z in
      let c := ((a - b + mod_const) mod mod_const)%Z in
      (Ndigits.N2Bv_sized s (Z.to_N c))
    | Index n o => fun x =>
      nth_default (kind_default _) (bitvec_to_nat (fst (snd x))) (fst x)
    | Cons n o => fun '(x, (v,_)) => (x :: v)
    | Snoc n o => fun '(v, (x,_)) => snoc v x

    | Concat n m o => fun '(x, (y, _)) => Vector.append x y
    end.
