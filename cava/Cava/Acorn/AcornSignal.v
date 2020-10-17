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
  | VoidType : SignalType                      (* An empty type *)
  | BitType : SignalType                       (* A single wire *)
  | VecType : SignalType -> nat -> SignalType  (* Vectors, possibly nested *)
  | ExternalType : string -> SignalType        (* An uninterpreted type *)
  | PairType : SignalType -> SignalType -> SignalType. (* A tuple *)

Inductive Signal : SignalType -> Type :=
  | Const0 : Signal BitType
  | Const1 : Signal BitType
  | Void : Signal VoidType
  | Wire : N -> Signal BitType
  | Vec : forall {t : SignalType} {s : nat}, Vector.t (Signal t) s -> Signal (VecType t s)
  | IndexSignal : forall {t : SignalType} {s : nat},
                  Signal (VecType t s) -> nat -> Signal t
  | Pair : forall {A B : SignalType}, Signal A -> Signal B -> Signal (PairType A B)
  | Fst : forall {A B : SignalType}, Signal (PairType A B) -> Signal A
  | Snd : forall {A B : SignalType}, Signal (PairType A B) -> Signal B.

Definition peel {k: SignalType} {s: nat} (v: Signal (VecType k s)) :
                Vector.t (Signal k) s :=
  Vector.map (IndexSignal v) (vseq 0 s).

Fixpoint denoteCombinaional (t : SignalType) : Type :=
  match t with
  | VoidType => unit
  | BitType => bool
  | VecType vt s => Vector.t (denoteCombinaional vt) s
  | ExternalType _ => string
  | PairType A B => denoteCombinaional A * denoteCombinaional B
  end.

Definition denoteSignal (t : SignalType) : Type := Signal t.
