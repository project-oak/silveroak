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

Require Import Coq.Program.Basics.
From Coq Require Import Strings.Ascii Strings.String.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
(* From Coq Require Import Numbers.NaryFunctions.
From Coq Require Import Init.Datatypes. *)
Require Import ExtLib.Structures.Monads.

Import ListNotations.
Import MonadNotation.
Open Scope list_scope.
Open Scope monad_scope.

From Cava Require Import Kind.
From Cava Require Import Signal.
From Cava Require Import VectorUtils.

Require Import Coq.Program.Program.
Require Import Coq.Init.Nat Coq.Arith.Arith Coq.micromega.Lia.

(******************************************************************************)
(* shape describes the types of wires going into or out of a Cava circuit,    *)
(* but not all shapes can be bound to a SystemVerilog port name. Those that   *)
(* can are identified by the One constructor.                                 *)
(******************************************************************************)

Inductive shape {A: Type} : Type :=
  | Empty : shape
  | One : A -> shape
  | Tuple2 : shape -> shape -> shape. (* A pair of bundles of wires *)

(* Notation "<< x >>" := (Tuple2 x Empty).
Notation "<< x , y , .. , z >>" := (Tuple2 x (Tuple2 y .. (Tuple2 z Empty) ..) ). *)

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

Fixpoint denote (doSomethingToOne : Kind -> Type) (k : @shape Kind) : Type :=
  match k with
  | Empty => unit
  | One thing => doSomethingToOne thing
  | Tuple2 a b => (denote doSomethingToOne a) * (denote doSomethingToOne b)
  end.

(*
Drop the rightmost element of a tuple structure if it is Empty. e.g.

withoutRightmostUnit ( Tuple2 x (Tuple2 y (Tuple2 z Empty)) )
                     = Tuple2 x (Tuple2 y z)
*)
Fixpoint withoutRightmostUnit {A} (s: @shape A): shape :=
  match s with
  | Empty => Empty
  | One thing => One thing
  | Tuple2 t1 Empty => t1
  | Tuple2 t1 t2 =>  Tuple2 t1 (withoutRightmostUnit t2)
  end.

(* Convert values to shape values *)

Class ToShape {a} t := {
  toShape: t -> @shape a;
}.

Instance ShapeNone {A}: @ToShape A unit := {
   toShape _ := Empty;
}.

Instance ShapeOne {A: Type}: ToShape A := {
   toShape t := One t;
}.

Instance ToShapePair2 {A t1 t2 : Type} `{@ToShape A t1} `{@ToShape A t2}:
                     @ToShape A (t1 * t2) := {
  toShape '(a, b) := @Tuple2 A (toShape a) (toShape b);
}.

Notation bundle := (@shape Kind).

Fixpoint denoteVecWith {A : Type} (T : Type) (n : list A) : Type :=
  match n with
  | [] => T
  | [x] => list T
  | x::xs => list (denoteVecWith T xs)
  end.

Fixpoint denoteKindWith (k : Kind) (T : Type) : Type :=
  match k with
  | Kind.Void => unit
  | Kind.Bit => T
  | Kind.Vec k2 s => Vector.t (denoteKindWith k2 T) s
  | Kind.ExternalType t => T
  end.

Fixpoint bitsInPort (p : Kind) : nat :=
  match p with
  | Kind.Void => 0
  | Kind.Bit => 1
  | Kind.Vec xs sz => sz * bitsInPort xs
  | Kind.ExternalType _ => 0
  end.

Fixpoint bitsInPortShape (s : bundle) : nat :=
  match s with
  | Empty => 0
  | One typ => bitsInPort typ
  | Tuple2 t1 t2 => bitsInPortShape t1 + bitsInPortShape t2
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

Lemma signal_tuple_is_tuple:
  forall a b t,
  signalTy (Signal t) (Tuple2 a b)
  = (signalTy (Signal t) a * signalTy (Signal t) b)%type.
Proof.
  intros.
  simpl.
  f_equal.
Defined.

(*
Given a signal of some shape 'withoutRightmost S',
we can extend it with a rightmost value of tt to get a signal of shape 'S'.
*)
Fixpoint insertRightmostTt {A t}
  (s: signalTy (Signal t) (withoutRightmostUnit A)) {struct A}
  : signalTy (Signal t) A.
Proof.
  induction A; simpl in *.
  exact tt.
  exact s.
  destruct A2.
  - exact (s, tt).
  - exact s.
  - rewrite signal_tuple_is_tuple in s.
    refine ((fst s, _)).
    apply snd in s.
    apply IHA2.
    apply s.
Defined.

(*
Given some function 'f' which takes as input a signal of shape 'A',
we can return a function performing 'f' that takes an input of
shape 'withoutRightmostUnit A' by first applying 'insertRightmostTt'
and then performing 'f'.
*)
Definition removeRightmostUnit {A B t}
  (f: signalTy (Signal t) A -> B)
  : signalTy (Signal t) (withoutRightmostUnit A) -> B :=
  fun a => f (insertRightmostTt a).
