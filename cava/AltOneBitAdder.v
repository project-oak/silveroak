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


Definition reorg1Fn {cin a b : signal}
                    (cinab : NetExpr \u27e8cin, \u27e8a, b\u3009\u3009) : NetExpr \u27e8\u27e8cin, a\u3009, \u27e8a, b\u3009\u3009
  := match cinab with
       NetPair cin ab => match ab with
                           NetPair a b => NetPair (NetPair cin a) (NetPair a b)
                         end
     end.

Definition reorg1 : cava \u27e8Bit, \u27e8Bit, Bit\u3009\u3009 \u27e8\u27e8Bit, Bit\u3009, \u27e8Bit, Bit\u3009\u3009
           := Rewire reorg1Fn.

Definition reorg2Fn (cinaps : NetExpr \u27e8\u27e8Bit, Bit\u3009, Bit\u3009) :
                    NetExpr\u27e8\u27e8Bit, Bit\u3009, \u27e8Bit, \u27e8Bit, Bit\u3009\u3009\u3009
  := match cinaps with
       @NetPair (Tuple2 Bit Bit) Bit cina ps
          => match cina with
                @NetPair Bit Bit cin a => NetPair (NetPair cin ps) (NetPair ps (NetPair a cin))
             end
     end.

Definition reorg2 := Rewire reorg2Fn.

Definition oneBitAdder : cava \u27e8Bit, \u27e8Bit, Bit\u3009\u3009 \u27e8Bit, Bit\u3009
  := reorg1 \u27fc second Xor2 \u27fc reorg2 \u27fc (Xorcy \u2016 Muxcy).

Definition oneBitAdder_top
  := (Input "cin" \u2016 (Input "a" \u2016 Input "b")) \u27fc
     oneBitAdder \u27fc
     ((Output "sum") \u2016 (Output "cout")).
