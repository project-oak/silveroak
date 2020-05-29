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

Require Import Program.Basics.
From Coq Require Import Ascii String.
From Coq Require Import ZArith.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
(* From Coq Require Import Numbers.NaryFunctions.
From Coq Require Import Init.Datatypes. *)
Require Import ExtLib.Structures.Monads.

Import ListNotations.
Import MonadNotation.
Open Scope list_scope.
Open Scope monad_scope.

From Cava Require Import Signal.

(******************************************************************************)
(* shape describes the types of wires going into or out of a Cava circuit,    *)
(* but not all shapes can be bound to a SystemVerilog port name. Those that   *)
(* can are identified by the One constructor.                                 *)
(******************************************************************************)

Inductive shape {A: Type} : Type :=
  | Empty : shape
  | One : A -> shape
  | Tuple2 : shape -> shape -> shape. (* A pair of bundles of wires *)

Notation "<< x >>" := (Tuple2 x Empty).
Notation "<< x , y , .. , z >>" := (Tuple2 x (Tuple2 y .. (Tuple2 z Empty) ..) ).

(* General tuples can be mapped to Tuple2 *)

(* TODO(satnam): It would be more useful to build a left-associative
   tuple.
*)
Fixpoint tuple {A: Type} (t : list shape) : shape :=
  match t with
  | [] => Empty
  | [x] => x
  | x::xs => @Tuple2 A x (tuple xs)
  end.

(* Supporting mapping over a shape. *)

Fixpoint mapShape {A B : Type} (f : A -> B) (s : @shape A) : @shape B :=
  match s with
  | Empty => Empty
  | One thing => One (f thing)
  | Tuple2 t1 t2 => Tuple2 (mapShape f t1) (mapShape f t2)
  end.

Fixpoint mapShapeM {A B : Type} {m} `{Monad m} (f : A -> m B) (s : @shape A) :
                  m (@shape B) :=
  match s with
  | Empty => ret Empty
  | One thing => fv <- f thing ;;
                 ret (One fv)
  | @Tuple2 _ t1 t2 => fv1 <- @mapShapeM A B m _ f t1 ;;
                       fv2 <- @mapShapeM A B m _ f t2 ;;
                       ret (Tuple2 fv1 fv2)
  end.

Definition mapShapeM_ {A : Type} {m} `{Monad m} (f : A -> m unit) (s : @shape A) :
                      m unit :=
  _ <- mapShapeM f s ;;
  ret tt.

Fixpoint zipShapes {A B : Type} (sA : @shape A) (sB : @shape B) :
                   @shape (A * B) :=
  match sA, sB with
  | Empty, Empty => Empty
  | One a, One b => One (a, b)
  | Tuple2 t1 t2, Tuple2 t3 t4 => Tuple2 (zipShapes t1 t3) (zipShapes t2 t4)
  | _, _ => Empty
  end.

Fixpoint flattenShape {A} (s : @shape A) : list A :=
  match s with
  | Empty => []
  | One thing => [thing]
  | Tuple2 t1 t2 =>  flattenShape t1 ++ flattenShape t2
  end.

(******************************************************************************)
(* Values of Kind can occur as the type of signals on a circuit interface *)
(******************************************************************************)

Inductive Kind : Type :=
  | Bit : Kind                (* A single wire *)
  | BitVec : list nat -> Kind (* Multi-dimensional bit-vectors *).

Notation bundle := (@shape Kind).

Fixpoint denoteBitVecWith {A : Type} (T : Type) (n : list A) : Type :=
  match n with
  | [] => T
  | [x] => list T
  | x::xs => list (denoteBitVecWith T xs)
  end.

Definition denoteKindWith (k : Kind) (T : Type) : Type :=
  match k with
  | Bit => T
  | BitVec v => denoteBitVecWith T v
  end.

Fixpoint bitsInPort (p : Kind) : nat :=
  match p with
  | Bit => 1
  | BitVec xs => fold_left (fun x y => x * y) xs 1
  end.

Fixpoint bitsInPortShape (s : bundle) : nat :=
  match s with
  | Empty => 0
  | One typ => bitsInPort typ
  | Tuple2 t1 t2 => bitsInPortShape t1 + bitsInPortShape t2
  end.

(* The duplicated i and l pamrameters are a temporary work-around to allow
   well-founded recursion to be recognized.
   TODO(satnam): Rewrite with an appropriate well-foundedness proof.
*)
Fixpoint numberBitVec (offset : N) (i : list nat) (l : list nat) : @denoteBitVecWith nat Signal l :=
  match l, i return @denoteBitVecWith nat Signal l with
  | [], _         => Vcc
  | [x], [_]      => map (compose Wire N.of_nat) (seq (N.to_nat offset) x)
  | x::xs, p::ps  => let z := N.of_nat (fold_left (fun x y => x * y) xs 1) in
                     map (fun w => numberBitVec (offset+w*z) ps xs) (map N.of_nat (seq 0 x))
  | _, _          => []
  end.

(* smashBitVec is like numberBitVec but returns the symbolic name and index
   for the vector shape.
*)
Fixpoint smashBitVec (name: string) (i: list nat) (l: list nat) (prefix: list nat) : @denoteBitVecWith nat Signal i :=
  match i, l return @denoteBitVecWith nat Signal i with
  | [], _        => Vcc
  | [x], _       => map (fun i => NamedBitVec name (prefix ++ [i])) (seq 0 x)
  | x::xs, y::ys => map (fun  xv => smashBitVec name xs ys (prefix ++ [xv])) (seq 0 x)
  | _, _         => []
  end. 

Fixpoint mapBitVec {A B} (f: A -> B) (i : list nat) (l : list nat) : @denoteBitVecWith nat A l -> @denoteBitVecWith nat B l :=
  match l, i  return @denoteBitVecWith nat A l -> @denoteBitVecWith nat B l with
  | [], _         => f
  | [x], [_]      => map f
  | x::xs, p::ps  => map (mapBitVec f ps xs)
  | _, _          => fun _ => []
  end.

Fixpoint zipBitVecs {A B} (i : list nat) (l : list nat)
  : @denoteBitVecWith nat A l -> @denoteBitVecWith nat B l -> @denoteBitVecWith nat (A*B) l :=
  match l, i  return @denoteBitVecWith nat A l -> @denoteBitVecWith nat B l -> @denoteBitVecWith nat (A*B) l with
  | [], _         => pair
  | [x], [_]      => fun ms ns => combine ms ns
  | x::xs, p::ps  => fun ms ns => map (fun '(m,n) => zipBitVecs ps xs m n) (combine ms ns)
  | _, _          => fun _ _ => []
  end.

Fixpoint flattenBitVec {A} (i : list nat) (l : list nat)
  : @denoteBitVecWith nat A l -> list A :=
  match l, i  return @denoteBitVecWith nat A l -> list A with
  | [], _         => fun z => [z]
  | [x], [_]      => fun zs => zs
  | x::xs, p::ps  => fun zs => concat (map (flattenBitVec ps xs) zs)
  | _, _          => fun _ => []
  end.

Definition flattenPort {A} (port: Kind) (x: denoteKindWith port A) : list A :=
  match port, x with
  | Bit, _ => [x]
  | BitVec sz, _ => flattenBitVec sz sz x
  end.

(******************************************************************************)
(* signalTy maps a shape to a type based on T                                 *)
(******************************************************************************)

Fixpoint signalTy (T : Type) (s : shape) : Type :=
  match s with
  | Empty  => unit
  | One t => denoteKindWith t T
  | Tuple2 s1 s2  => prod (signalTy T s1) (signalTy T s2)
  end.

Fixpoint numberPort (i : N) (inputs: bundle) : signalTy Signal inputs :=
  match inputs return signalTy Signal inputs with
  | Empty => tt
  | One typ =>
      match typ return denoteKindWith typ Signal with
      | Bit => Wire i
      | BitVec xs => numberBitVec i xs xs
      end
  | Tuple2 t1 t2 => let t1Size := bitsInPortShape t1 in
                    (numberPort i t1,  numberPort (i + N.of_nat t1Size) t2)
  end.
