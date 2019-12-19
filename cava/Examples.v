(****************************************************************************)
(* Copyright 2019 The Project Oak Authors                                   *)
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

(* A codification of the Lava embedded DSL develope for Haskell into
   Coq for the specification, implementaiton and formal verification of circuits.
   Experimental work, very much in flux, as Satnam learns Coq!
*)

Require Import Program.Basics.
From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.State.

Require Import Cava.

Local Open Scope list_scope.
Local Open Scope monad_scope.

(* Experiments with the pre-defined gates. *)

Eval simpl in fst ((inv false) tt). 
Eval simpl in fst ((inv true) tt).

Eval simpl in fst ((and2 (false, false)) tt).
Eval simpl in fst ((and2 (true, true)) tt).

Eval cbv in ((inv 0) (mkCavaState 1 [])).

(* NAND gate examples. *)

Definition nand2 {m t} `{Monad m} `{Cava m t} := and2 >=> inv.

Eval cbv in ((nand2 (0, 1)) (mkCavaState 2 [])).

Eval simpl in fst ((nand2 (false, false)) tt).
Eval simpl in fst ((nand2 (true, true)) tt).