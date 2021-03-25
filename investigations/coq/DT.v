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

Inductive alt (A : Type) :=
  | One : A -> alt A
  | Two : A -> A -> alt A.

Definition ex1 : alt nat := One nat 42.
Definition ex2 : alt nat := Two nat 87 12.

Inductive expr : Type -> Type :=
  | BoolConst : bool -> expr bool
  | NatConst : nat -> expr nat
  | If : forall (A : Type), expr bool -> expr A -> expr A -> expr A
  | Plus : expr nat -> expr nat -> expr nat
  .

Definition double (v : expr nat) : expr nat :=
  match v with
  | NatConst n => Plus n n
  | Plus a b => Plus v v
  end.
