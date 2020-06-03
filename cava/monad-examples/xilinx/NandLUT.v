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

From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
From Coq Require Import ZArith.
Import ListNotations.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Monad.Cava.
Require Import Cava.Monad.Combinators.
Require Import Cava.BitArithmetic.
Require Import Cava.Netlist.
Require Import Cava.Types.
Require Import Cava.Monad.XilinxAdder.

Local Open Scope list_scope.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Definition lutNAND {m bit} `{Cava m bit} (i0i1 : bit * bit) : m bit :=
  x <- lut2 (andb) i0i1 ;;
  z <- lut1 (negb) x ;;
  ret z.

Definition lutNANDInterface
  := mkCombinationalInterface "lutNAND"
     (Tuple2 (One ("a", Bit)) (One ("b", Bit)))
     (One ("c", Bit))
     [].

Definition lutNANDNetlist := makeNetlist lutNANDInterface lutNAND.

 Definition lutNAND_tb_inputs : list (bool * bool) :=
 [(false, false); (false, true); (true, false); (true, true)].

 Definition lutNAND_tb_expected_outputs : list bool :=
  map (fun i => combinational (lutNAND i)) lutNAND_tb_inputs.

Definition lutNAND_tb :=
  testBench "lutNAND_tb" lutNANDInterface
  lutNAND_tb_inputs lutNAND_tb_expected_outputs.
