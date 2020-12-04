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

Require Import Coq.Strings.String.
Require Import Coq.Vectors.Vector.

Require Import Cava.VectorUtils.

(******************************************************************************)
(* Values of Kind can occur as the type of signals on a circuit interface *)
(******************************************************************************)

Inductive Kind : Type :=
  | Void : Kind                    (* An empty type *)
  | Bit : Kind                     (* A single wire *)
  | Vec : Kind -> nat -> Kind      (* Vectors, possibly nested *)
  | ExternalType : string -> Kind. (* An uninterpreted type *)
