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

Require Import Coq.Strings.Ascii Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Cava.
Require Import Cava.Cava.
Existing Instance CavaCombinationalNet.

Definition lutNAND {signal} `{Cava signal}
           (i0i1 : signal Bit * signal Bit) : cava (signal Bit) :=
  x <- lut2 (andb) i0i1 ;;
  z <- lut1 (negb) x ;;
  ret z.

Definition lutNANDInterface
  := combinationalInterface "lutNAND"
     [mkPort "a"  Bit; mkPort "b" Bit]
     [mkPort "c" Bit].

Definition lutNANDNetlist := makeNetlist lutNANDInterface lutNAND.

 Definition lutNAND_tb_inputs : list (bool * bool) :=
 [(false, false); (false, true); (true, false); (true, true)].

 Definition lutNAND_tb_expected_outputs : list bool :=
   simulate (Comb lutNAND) lutNAND_tb_inputs.

Definition lutNAND_tb :=
  testBench "lutNAND_tb" lutNANDInterface
  lutNAND_tb_inputs lutNAND_tb_expected_outputs.
