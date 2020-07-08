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
From Coq Require Import Vector.

From Cava Require Import Kind.
From Cava Require Import VectorUtils.

Inductive Signal : Kind -> Type :=
  | UndefinedSignal : Signal Void
  | UninterpretedSignal: forall {t}, string -> Signal (ExternalType t)
  | Gnd: Signal Bit
  | Vcc: Signal Bit
  | Wire: N -> Signal Bit
  | NamedWire: string -> Signal Bit
  | NamedVector: forall k s, string -> Signal (BitVec k s)
  | LocalBitVec: forall k s, N -> Signal (BitVec k s)
  | VecLit: forall {k s}, Vector.t (Signal k) s -> Signal (BitVec k s)
  (* Dynamic index *)
  | IndexAt:  forall {k sz isz}, Signal (BitVec k sz) ->
              Signal (BitVec Bit isz) -> Signal k
  (* Static indexing *)
  | IndexConst: forall {k sz}, Signal (BitVec k sz) -> nat -> Signal k
  (* Static slice *)
  | Slice: forall {k sz} (start len: nat), Signal (BitVec k sz) ->
                                           Signal (BitVec k len).

(* A default unsmashed value for a given Kind. *)
Fixpoint defaultKindSignal (k: Kind) : Signal k :=
  match k with
  | Void => UndefinedSignal
  | Bit => Gnd
  | BitVec k s => VecLit (Vector.const (defaultKindSignal k) s)
  | ExternalType s => UninterpretedSignal "default-error"
  end.

