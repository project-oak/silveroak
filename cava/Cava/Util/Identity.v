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

Require Import Coq.Vectors.Vector.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Vector.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Structures.Traversable.
Require Import Cava.Util.Vector.

(* Identity monad *)
Definition ident (T : Type) := T.
Instance Monad_ident : Monad ident :=
  { ret := fun _ t => t;
    bind := fun _ _ x f => f x }.

Instance MonadLaws_ident : MonadLaws Monad_ident.
Proof. econstructor; intros; exact eq_refl. Defined.
