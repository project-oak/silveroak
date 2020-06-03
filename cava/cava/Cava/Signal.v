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

From Coq Require Import Ascii String.
From Coq Require Import ZArith.

Inductive Signal : Type :=
  | UndefinedSignal : Signal
  | Gnd: Signal
  | Vcc: Signal
  | Wire: N -> Signal
  | NamedWire: string -> Signal
  | NamedBitVec: string -> list nat -> Signal
  | Vec: list Signal -> Signal.
