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

Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.

(* There are multiple ways to generalize ExtLib.Functor, this is particular one
   is useful for working with "higher kinded data". *)
(* TODO(blaxill): see if coq-ext-lib has interest in adding these definitions *)

Class FFunctor {k} (F: (k -> Type) -> Type) :=
{ ffmap : forall {A B : (k -> Type)}, (forall x, A x -> B x) -> F A -> F B }.

Class FTraversable {k} (T: (k -> Type) -> Type): Type :=
{ fmapT : forall {A B : (k -> Type)} {F : Type -> Type} {Ap:Applicative F},
    (forall x, A x -> F (B x)) -> T A -> F (T B) }.

Definition sequence {k} {T : (k -> Type) -> Type}
          {Tr: FTraversable T} {F : Type -> Type} {Ap:Applicative F} {A}
: T (fun x => F (A x)) -> F (T A) := @fmapT k T _ (fun x => F (A x)) A F _ (fun _ f => f).

Class FZip {k} (T: (k -> Type) -> Type): Type :=
{ fzip : forall {A B C: (k -> Type)}, (forall {x}, A x -> B x -> C x) -> T A -> T B -> T C }.
