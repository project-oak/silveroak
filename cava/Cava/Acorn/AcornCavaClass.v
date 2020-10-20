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

Class Cava m `{Monad m} (signal : SignalType -> Type) := {
  one : signal BitType;
  zero : signal BitType;
  inv : signal BitType -> m (signal BitType);
  and2 : signal BitType * signal BitType -> m (signal BitType);
  or2 : signal BitType * signal BitType -> m (signal BitType);
  xor2 : signal BitType * signal BitType -> m (signal BitType);
  pair : forall {A B : SignalType}, signal A -> signal B -> signal (PairType A B);
  fsT : forall {A B : SignalType}, signal (PairType A B) -> signal A;
  snD : forall {A B : SignalType}, signal (PairType A B) -> signal B;
}.

Definition unpair {m signal} `{Cava m signal}
          {A B : SignalType}
          (ab: signal (PairType A B)) : (signal A * signal B) :=
  (fsT ab, snD ab).