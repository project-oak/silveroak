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
From Coq Require Import Lists.List.
Import ListNotations.
Open Scope list_scope.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.StateMonad.
Import MonadNotation.
Open Scope monad_scope.

From Cava Require Import Acorn.AcornSignal.
From Cava Require Import Acorn.AcornNetlist.


Record AcornModule : Type := mkAcornModule{
  moduleName : string;
  netlist : AcornNetlist;
}.

Record AcornState : Type := mkAcornState {
  netNumber : N;
  module : AcornModule;
}.

Definition getNetNumber : state AcornState N :=
  acornState <- get ;;
  match acornState with
  | mkAcornState netNr _ => ret netNr
  end.


Definition incrementNetNumber : state AcornState unit :=
  acornState <- get ;;
  match acornState with
  | mkAcornState netNr m =>
     put (mkAcornState (netNr + 1) m)
  end.  

Definition newWire : state AcornState (Signal Bit) :=
  netNr <- getNetNumber ;;
  incrementNetNumber ;;
  ret (Wire netNr).

Definition addInstance (newInst : AcornInstance) : state AcornState unit :=
 acornState <- get ;;
 match acornState with
 | mkAcornState netNr (mkAcornModule name nl) =>
     put (mkAcornState netNr (mkAcornModule name (newInst::nl)))
 end.
