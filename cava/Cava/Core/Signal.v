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

Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.Vectors.Vector.

(******************************************************************************)
(* The types of signals that can flow over wires, used to index signal        *)
(******************************************************************************)

Inductive SignalType :=
  | Void : SignalType                              (* An empty type *)
  | Bit : SignalType                               (* A single wire *)
  | Vec : SignalType -> nat -> SignalType              (* Vectors, possibly nested *)
  | ExternalType : string -> SignalType.            (* An uninterpreted type *)

(* one or more signals *)
Inductive type : Type :=
| tone (t : SignalType)
| tpair (t1 t2 : type)
.

(* Notation for signals and collections of signals *)
Declare Scope signal_scope.
Delimit Scope signal_scope with signal.
Bind Scope signal_scope with type.
Coercion tone : SignalType >-> type.
Infix "*" := tpair : signal_scope.

(******************************************************************************)
(* Combinational denotion of the SignalType and default values.               *)
(******************************************************************************)

Fixpoint signal (t: SignalType) : Type :=
  match t with
  | Void => unit
  | Bit => bool
  | Vec vt sz => Vector.t (signal vt) sz
  | ExternalType _ => unit (* No semantics for combinational interpretation. *)
  end.

Fixpoint value (t : type) : Type :=
  match t with
  | tone t => signal t
  | tpair t1 t2 => value t1 * value t2
  end.

Fixpoint default_signal (t: SignalType) : signal t :=
  match t  with
  | Void => tt
  | Bit => false
  | Vec t2 sz => Vector.const (default_signal t2) sz
  | ExternalType _ => tt
  end.

Fixpoint default_value (t: type) : value t :=
  match t with
  | tone t => default_signal t
  | tpair t1 t2 => (default_value t1, default_value t2)
  end.

(******************************************************************************)
(* Netlist AST representation for signal expressions.                         *)
(******************************************************************************)

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
  (* Dynamic index *)
  | IndexAt:  forall {t sz isz}, Signal (Vec t sz) ->
              Signal (Vec Bit isz) -> Signal t
  (* Static indexing *)
  | IndexConst: forall {t sz}, Signal (Vec t sz) -> nat -> Signal t
  (* Static slice *)
  | Slice: forall {t sz} (start len: nat), Signal (Vec t sz) ->
                                           Signal (Vec t len)
  (* Synthesizable arithmetic operations. *)
  | UnsignedAdd: forall {a b c : nat}, Signal (Vec Bit a) -> Signal (Vec Bit b) ->
                                       Signal (Vec Bit c)
  | UnsignedSubtract : forall {a b c : nat}, Signal (Vec Bit a) ->
                                        Signal (Vec Bit b) ->
                                        Signal (Vec Bit c)
  | UnsignedMultiply : forall {a b c : nat}, Signal (Vec Bit a) ->
                                        Signal (Vec Bit b) ->
                                        Signal (Vec Bit c)
  | GreaterThanOrEqual: forall {a b : nat}, Signal (Vec Bit a) ->
                                            Signal (Vec Bit b) ->
                                            Signal Bit.

Definition denoteSignal (t : SignalType) : Type := Signal t.

(* A default netlist value for a given SignalType. *)
Fixpoint defaultNetSignal (t: SignalType) : Signal t :=
  match t with
  | Void => UndefinedSignal
  | Bit => Gnd
  | Vec vt s => VecLit (Vector.const (defaultNetSignal vt) s)
  | ExternalType s => UninterpretedSignal "default-defaultSignal"
  end.

(* To allow us to represent a heterogenous list of Signal t values where
   the Signal t varies we make a wrapper that erase the Kind index type.
*)
Inductive UntypedSignal := USignal : forall {Kind}, Signal Kind -> UntypedSignal.
