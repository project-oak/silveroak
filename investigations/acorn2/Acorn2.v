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

Require Import Coq.Strings.Ascii Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.MonadState.

Require Import Coq.Numbers.DecimalString.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope type_scope.

Inductive SignalType :=
  | Bit : SignalType 
  | Nat : SignalType.

Inductive Signal : SignalType -> Type :=
  | BitType : N -> Signal Bit
  | NatType : N -> Signal Nat.

Inductive Acorn : Type -> Type :=
| Inv : Signal Bit -> Signal Bit -> Acorn (Signal Bit -> Signal Bit)
| And2 : Signal Bit -> Signal Bit -> Signal Bit -> Acorn (Signal Bit * Signal Bit -> Signal Bit)
| Compose : forall {t1 t2 t3}, Acorn (t1 -> t2) -> Acorn (t2 -> t3) -> Acorn (t1 -> t3).

Definition nandGate : Acorn (Signal Bit * Signal Bit -> Signal Bit)
  := Compose (And2 (BitType 1) (BitType 2) (BitType 3))
             (Inv (BitType 3) (BitType 4)).

