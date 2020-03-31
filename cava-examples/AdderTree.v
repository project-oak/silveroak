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

(* A codification of the Lava embedded DSL develope for Haskell into
   Coq for the specification, implementaiton and formal verification of
   circuits. Experimental work, very much in flux, as Satnam learns Coq!
*)

Require Import Program.Basics.
From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
From Coq Require Import NArith.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

Require Import Cava.Cava.
Require Import Cava.Combinators.
Require Import Cava.Netlist.
Require Import Cava.BitArithmetic.

Local Open Scope list_scope.
Local Open Scope monad_scope.


Definition adder_3in {m bit} `{Cava m bit} {aL bL cL : nat}
                     (a : (Vector.t bit aL))
                     (b : (Vector.t bit bL))
                     (c : (Vector.t bit cL))
                     : m (Vector.t bit (max (max aL bL + 1) cL + 1)) :=
  a_plus_b <- unsignedAdd a b ;;
  sum <- unsignedAdd a_plus_b c ;;
  ret sum.


Definition adder8_3inTop : state CavaState (Vector.t N 10) :=
  setModuleName "adder8_3in" ;;
  a <- inputVectorTo0 8 "a" ;;
  b <- inputVectorTo0 8 "b" ;;
  c <- inputVectorTo0 8 "c" ;;
  sum <- adder_3in a b c ;;
  outputVectorTo0 10 sum "sum".

Definition adder8_3inNetlist := makeNetlist adder8_3inTop.
  
