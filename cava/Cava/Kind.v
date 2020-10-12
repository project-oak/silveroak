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

From Coq Require Import String.
From Coq Require Import Vector.

(******************************************************************************)
(* Values of Kind can occur as the type of signals on a circuit interface *)
(******************************************************************************)

Inductive Kind : Type :=
  | Void : Kind                    (* An empty type *)
  | Bit : Kind                     (* A single wire *)
  | BitVec : Kind -> nat -> Kind   (* Vectors, possibly nested *)
  | ExternalType : string -> Kind. (* An uninterpreted type *)

Fixpoint listOfVecTy (bv: Kind) : Type :=
  match bv with
  | Void => list bool
  | Bit => list bool
  | BitVec k2 _ => list (listOfVecTy k2)
  | ExternalType _ => list bool
  end.
