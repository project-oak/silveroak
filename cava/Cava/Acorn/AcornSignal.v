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

From Coq Require Import ZArith.
From Coq Require Import String.
From Coq Require Import Vector.

From Cava Require Import VectorUtils.

Inductive SignalType :=
  | Void : SignalType                             (* An empty type *)
  | Bit : SignalType                              (* A single wire *)
  | Vec : SignalType -> nat -> SignalType         (* Vectors, possibly nested *)
  | ExternalType : string -> SignalType           (* An uninterpreted type *)
  | Pair : SignalType -> SignalType -> SignalType. (* A tuple *)

Inductive Signal : SignalType -> Type :=
  | Const0 : Signal Bit
  | Const1 : Signal Bit
  | MkVoid : Signal Void
  | Wire : N -> Signal Bit
  | VecLit : forall {t : SignalType} {s : nat}, Vector.t (Signal t) s -> Signal (Vec t s)
  | IndexSignal : forall {t : SignalType} {s : nat},
                  Signal (Vec t s) -> nat -> Signal t
  | MkPair : forall {A B : SignalType}, Signal A -> Signal B -> Signal (Pair A B)
  | Fst : forall {A B : SignalType}, Signal (Pair A B) -> Signal A
  | Snd : forall {A B : SignalType}, Signal (Pair A B) -> Signal B.

Fixpoint denoteCombinational (t : SignalType) : Type :=
  match t with
  | Void => unit
  | Bit => bool
  | Vec vt s => Vector.t (denoteCombinational vt) s
  | ExternalType _ => string
  | Pair A B => denoteCombinational A * denoteCombinational B
  end.

Definition denoteSignal (t : SignalType) : Type := Signal t.
