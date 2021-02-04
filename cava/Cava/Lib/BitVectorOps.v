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

Require Import Coq.Vectors.Vector.
Import VectorNotations.
Local Open Scope vector_scope.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Export MonadNotation.
Open Scope monad_scope.

Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.

Section WithCava.
  Context {signal} `{Cava signal}.

  (* A circuit to xor two bit-vectors *)
  Definition xorV {n : nat} (ab: signal (Vec Bit n) * signal (Vec Bit n)) :
    cava (signal (Vec Bit n)) :=
    zipWith xor2 (fst ab) (snd ab).

  (* Make a curried version of xorV *)
  Definition xorv {n} (a b : signal (Vec Bit n)) : cava (signal (Vec Bit n)) := xorV (a, b).

End WithCava.
