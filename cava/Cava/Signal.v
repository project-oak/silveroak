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

From Coq Require Import Strings.Ascii Strings.String.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Vectors.Vector.

From Cava Require Import Kind.
From Cava Require Import VectorUtils.

Inductive SignalType :=
  | Void : SignalType                              (* An empty type *)
  | Bit : SignalType                               (* A single wire *)
  | Vec : SignalType -> nat -> SignalType          (* Vectors, possibly nested *)
  | ExternalType : string -> SignalType            (* An uninterpreted type *)
  | Pair : SignalType -> SignalType -> SignalType. (* A tuple *)

Inductive Signal : SignalType -> Type :=
  | UndefinedSignal : Signal Void
  | UninterpretedSignal: forall {t: string}, string -> Signal (ExternalType t)
  | UninterpretedSignalIndex: forall (t: string), N -> Signal (ExternalType t)
  | SelectField: forall {t1: SignalType} (t2: SignalType), Signal t1 -> string -> Signal t2
  | Gnd: Signal Bit
  | Vcc: Signal Bit
  | Wire: N -> Signal Bit
  | NamedWire: string -> Signal Bit
  | NamedVector: forall t s, string -> Signal (Vec t s)
  | LocalVec: forall t s, N -> Signal (Vec t s)
  | VecLit: forall {t s}, Vector.t (Signal t) s -> Signal (Vec t s)
  | MkPair : forall {A B : SignalType}, Signal A -> Signal B -> Signal (Pair A B)
  (* Dynamic index *)
  | IndexAt:  forall {t sz isz}, Signal (Vec t sz) ->
              Signal (Vec Bit isz) -> Signal t
  (* Static indexing *)
  | IndexConst: forall {t sz}, Signal (Vec t sz) -> nat -> Signal t
  (* Static slice *)
  | Slice: forall {t sz} (start len: nat), Signal (Vec t sz) ->
                                           Signal (Vec t len).

Definition denoteSignal (t : SignalType) : Type := Signal t.

(* A default value for a given SignalType. *)
Fixpoint defaultSignal (t: SignalType) : Signal t :=
  match t with
  | Void => UndefinedSignal
  | Bit => Gnd
  | Vec vt s => VecLit (Vector.const (defaultSignal vt) s)
  | ExternalType s => UninterpretedSignal "default-defaultSignal"
  | Pair t1 t2 => MkPair (defaultSignal t1) (defaultSignal t2)
  end.

(* To allow us to represent a heterogenous list of Signal t values where
   the Signal t varies we make a wrapper that erase the Kind index type.
*)
Inductive UntypedSignal := USignal : forall {Kind}, Signal Kind -> UntypedSignal.

