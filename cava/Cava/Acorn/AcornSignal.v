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

From Coq Require Import ZArith.ZArith.
From Coq Require Import Strings.String.
From Coq Require Import Vectors.Vector.

From Coq Require Import Lists.List.
Import ListNotations.

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

Definition denoteSignal (t : SignalType) : Type := Signal t.

Fixpoint denoteCombinational (t : SignalType) : Type :=
  match t with
  | Void => unit
  | Bit => bool
  | Vec vt s => Vector.t (denoteCombinational vt) s
  | ExternalType _ => string
  | Pair A B => denoteCombinational A * denoteCombinational B
  end.

Local Open Scope list_scope.
Local Open Scope string_scope.

Definition t1 : ((nat * nat) * nat) := (1, 2, 3).
Definition t2 : ((nat * nat) * nat) := ((1, 2), 3).

Fixpoint denoteInterface' (denotion : SignalType -> Type)
                          (accum : Type) 
                          (v : list (string * SignalType))
                         : Type :=
  match v with
  | [] => accum
  | (n, t)::pds => denoteInterface' denotion (accum * denotion t) pds
  end.

Definition denoteInterface (denotion : SignalType -> Type)
                           (v : list (string * SignalType)) : Type :=
  match v with
  | [] => unit
  | (n, t)::pds => denoteInterface' denotion (denotion t) pds
  end.
