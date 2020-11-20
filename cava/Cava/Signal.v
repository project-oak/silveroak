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
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Vectors.Vector.

From Cava Require Import Kind.
From Cava Require Import VectorUtils.

(******************************************************************************)
(* The types of signals that can flow over wires, used to index signal        *)
(******************************************************************************)

Inductive SignalType :=
  | Void : SignalType                              (* An empty type *)
  | Bit : SignalType                               (* A single wire *)
  | Vec : SignalType -> nat -> SignalType          (* Vectors, possibly nested *)
  | ExternalType : string -> SignalType.           (* An uninterpreted type *)

(******************************************************************************)
(* Combinational denotion of the SignalType and default values.               *)
(******************************************************************************)

Fixpoint combType (t: SignalType) : Type :=
  match t with
  | Void => unit
  | Bit => bool
  | Vec vt sz => Vector.t (combType vt) sz
  | ExternalType _ => unit (* No semantics for combinational interpretation. *)
  end.

Fixpoint defaultCombValue (t: SignalType) : combType t :=
  match t  with
  | Void => tt
  | Bit => false
  | Vec t2 sz => Vector.const (defaultCombValue t2) sz
  | ExternalType _ => tt
  end.

(******************************************************************************)
(* Representation of circuit interface types with flat tuples.                *)
(******************************************************************************)

(* Right-associative tuples ending with a unit. *)

Fixpoint tupleInterfaceR (signal: SignalType -> Type) (v : list SignalType) : Type :=
  match v with
  | [] => unit
  | x :: pds => signal x * tupleInterfaceR signal pds
  end.


(* Left-associative tuples with no trailing unit. **)
Fixpoint tupleInterface' (signal: SignalType -> Type) accum (l : list SignalType) : Type :=
  match l with
  | [] => accum
  | x::xs => tupleInterface' signal (accum * signal x)%type xs
  end.

Definition tupleInterface (signal: SignalType -> Type) (l : list SignalType) : Type :=
  match l with
  | [] => unit
  | x::xs => tupleInterface' signal (signal x) xs
  end.

(* Convert a right-associative tuple to a left-associative tuple. *)
Fixpoint rebalance' (signal: SignalType -> Type)
                    (ts : list SignalType) {accumT : Type} (accum : accumT)
  : tupleInterfaceR signal ts -> tupleInterface' signal accumT ts :=
  match ts with
  | [] => fun _ : unit => accum
  | x::xs =>
    fun ab => rebalance' signal xs (accum, fst ab) (snd ab)
  end.

Definition rebalance (signal: SignalType -> Type)
                      (ts : list SignalType)
                      : tupleInterfaceR signal ts -> tupleInterface signal ts :=
  match ts with
  | [] => fun _ => tt
  | x::xs => fun ab => rebalance' signal xs (fst ab) (snd ab)
  end.

(* Convert a left-associative tuple to a right-associative tuple. *)
Fixpoint unbalance' (signal: SignalType -> Type)
                    (ts : list SignalType) {accumT : Type}
  : tupleInterface' signal accumT ts -> accumT * tupleInterfaceR signal ts :=
  match ts with
  | [] => fun (acc : accumT) => (acc, tt)
  | x::xs =>
    fun ab =>
      let '(acc, vx, vxs) := unbalance' signal xs ab in
      (acc, (vx, vxs))
  end.

Definition unbalance (signal: SignalType -> Type)
                     (ts : list SignalType)
                     : tupleInterface signal ts -> tupleInterfaceR signal ts :=
  match ts as ts0 return tupleInterface signal ts0 -> tupleInterfaceR signal ts0 with
  | [] => fun _ => tt
  | x::xs => unbalance' signal xs
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
                                           Signal (Vec t len).

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
