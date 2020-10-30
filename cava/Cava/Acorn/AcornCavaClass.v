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

Require Import ExtLib.Structures.Monads.

From Cava Require Import Acorn.AcornSignal.

Open Scope type_scope.

Class Cava (signal : SignalType -> Type) := {
  m : Type -> Type;
  one : signal Bit;
  zero : signal Bit;
  inv : signal Bit -> m (signal Bit);
  and2 : signal Bit * signal Bit -> m (signal Bit);
  or2 : signal Bit * signal Bit -> m (signal Bit);
  xor2 : signal Bit * signal Bit -> m (signal Bit);
  pair : forall {A B : SignalType}, signal A -> signal B -> signal (Pair A B);
  fsT : forall {A B : SignalType}, signal (Pair A B) -> signal A;
  snD : forall {A B : SignalType}, signal (Pair A B) -> signal B;
  peel : forall {s : nat} {k : SignalType}, signal (Vec k s) -> Vector.t (signal k) s;
  unpeel : forall {s : nat} {k : SignalType}, Vector.t (signal k) s -> signal (Vec k s);
}.

Definition unpair {signal} `{Cava signal}
          {A B : SignalType}
          (ab: signal (Pair A B)) : (signal A * signal B) :=
  (fsT ab, snD ab).
