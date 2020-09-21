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


From Cava Require Export Arrow.ArrowKind.

Local Notation "[ x ~~~> .. ~~~> y ]" := (Tuple x .. (Tuple y Unit) ..).

Notation vec_index n := (Vector Bit (Nat.log2_up n)).

(* TODO(blaxill): split type into e.g. unary binary etc ops? *)
Inductive CircuitPrimitive :=
  | Constant (ty: Kind) (v: denote_kind ty)
  | Delay (o: Kind)
  | Not
  | BufGate
  | Uncons (n: nat) (o: Kind)
  | Unsnoc (n: nat) (o: Kind)
  | Slice (n: nat) (x y: nat) (o: Kind)
  | Split (n m: nat) (o: Kind)
  | EmptyVec (o: Kind)
  | Lut (n: nat) (f: bool^^n --> bool)

  | And
  | Nand
  | Or
  | Nor
  | Xor
  | Xnor
  | Xorcy

  | Fst (x y: Kind)
  | Snd (x y: Kind)
  | Pair (x y: Kind)

  | Muxcy
  | UnsignedAdd (a b c: nat)
  | UnsignedSub (a: nat)
  | Index (n: nat) (o: Kind)
  | Cons (n: nat) (o: Kind)
  | Snoc (n: nat) (o: Kind)
  | Concat (n m: nat) (o: Kind).

Fixpoint primitive_input (op: CircuitPrimitive): Kind :=
  match op with
  | Constant _ _ => Unit
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

Fixpoint primitive_output (op: CircuitPrimitive): Kind :=
  match op with
  | Constant ty _ => ty
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
