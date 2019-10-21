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

Require Import AltCava.
From Coq Require Import Ascii String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Basics.
Local Open Scope program_scope.


Definition reorg1 (cinab : NetExpr (Tuple2 Bit (Tuple2 Bit Bit))) :
                  NetExpr (Tuple2 (Tuple2 Bit Bit) (Tuple2 Bit Bit))
  := match cinab with
     | NetPair cin (NetPair a b) => NetPair (NetPair cin a) (NetPair a b)
     end.

Definition oneBitAdder
  := Rewire reorg1 ⟼ second Xor2.



Definition forkBit (x : NetExpr Bit) : NetExpr (Tuple2 Bit Bit)
  := match x with
     | Net n => NetPair (Net n) (Net n)
     end.

 Definition swapBit (x : NetExpr (Tuple2 Bit Bit)) : NetExpr (Tuple2 Bit Bit)
  := match x with
     | NetPair a b => NetPair b a
     end.    