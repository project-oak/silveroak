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


Definition reorg1Fn {T : Type} {cin a b : signal}
                    (cinab : @Expr T ‹cin, ‹a, b››) : @Expr T ‹‹cin, a›, ‹a, b››
  := match cinab with
       NetPair cin ab => match ab with
                           NetPair a b => NetPair (NetPair cin a) (NetPair a b)
                         end
     end.

Definition reorg1 : cava ‹Bit, ‹Bit, Bit›› ‹‹Bit, Bit›, ‹Bit, Bit››
           := Rewire reorg1Fn.

Definition reorg2Fn (cinaps : Expr ‹‹Bit, Bit›, Bit›) :
                     Expr‹‹Bit, Bit›, ‹Bit, ‹Bit, Bit›››
  := match cinaps with
       @NetPair (Tuple2 Bit Bit) Bit cina ps
          => match cina with
                @NetPair Bit Bit cin a => NetPair (NetPair cin ps) (NetPair ps (NetPair a cin))
             end
     end.

Definition reorg2 := Rewire reorg2Fn.

Definition oneBitAdder : cava ‹Bit, ‹Bit, Bit›› ‹Bit, Bit›
  := reorg1  ⟼ second Xor2  ⟼ reorg2  ⟼ (Xorcy ‖ Muxcy).

Definition oneBitAdder_top
  := (Input "cin" ‖ (Input "a" ‖ Input "b"))  ⟼
     oneBitAdder  ⟼
     ((Output "sum") ‖ (Output "cout")).
