(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
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

Require Import  Coq.Lists.List.

Import ListNotations.

Module Vec1.
  Section Vector.
    Context (A: Type).
    Inductive Vector : nat -> Type :=
    | vec : forall (xs : list A), Vector (length xs).

    Definition nil : Vector 0 := vec [].

    Definition cons {n : nat} (x:A) (xs: Vector n): Vector (1 + n) :=
      match xs with
      | vec xs' => vec (x::xs')
      end.
  End Vector.

  Compute (cons nat 0 (cons nat 1 (cons nat 2 (nil nat)))).
End Vec1.

Module Vec2.
  Section Vector.
    Context (A: Type).
    Inductive Vector : nat -> Type :=
    | vec : forall (xs : list A) (len: nat), len = length xs -> Vector len.

    Definition nil : Vector 0 := vec [] _ eq_refl.

    Definition cons {n : nat} (x:A) (xs: Vector n): Vector (S n).
      refine (
      match xs with
      | vec xs' len h => vec (x::xs') _ _
      end).
      abstract (rewrite h; reflexivity).
    Defined.
  End Vector.

  Compute (cons nat 0 (cons nat 1 (cons nat 2 (nil nat)))).
End Vec2.

