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

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Require Import Acornish.ListUtils.

Import ListNotations.

Inductive SignalType :=
  | Bit : SignalType
  | Nat : SignalType.

Definition denoteSignal (t: SignalType) : Type :=
  match t with
  | Bit => bool
  | Nat => nat
  end.

Definition resetVal (t: SignalType) : denoteSignal t :=
  match t with
  | Bit => false
  | Nat => 0
  end.

Fixpoint resetVals (t: list SignalType) : denote_list denoteSignal t :=
  match t with
  | [] => tt
  | x :: xs => (resetVal x, resetVals xs)
  end.

Definition split_values {x y} := split_denotation (x:=x) (y:=y) denoteSignal.
Definition combine_values {x y} := combine_denotation (x:=x) (y:=y) denoteSignal.
