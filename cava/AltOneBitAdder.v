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


Definition reorg1 {cin a b : signal}
                  (cinab : NetExpr (Tuple2 cin (Tuple2 a b))) :
                  NetExpr (Tuple2 (Tuple2 cin a) (Tuple2 a b))
  := match cinab with
       NetPair cin ab => match ab with
                           NetPair a b => NetPair (NetPair cin a) (NetPair a b)
                         end
     end.


Definition reorg2 (cinaps : NetExpr (Tuple2 (Tuple2 Bit Bit) Bit)) :
                  NetExpr (Tuple2 (Tuple2 Bit Bit) (Tuple2 Bit (Tuple2 Bit Bit)))
  := match cinaps with
       @NetPair (Tuple2 Bit Bit) Bit cina ps
          => match cina with
                @NetPair Bit Bit cin a => NetPair (NetPair cin ps) (NetPair ps (NetPair a cin))
             end
     end.

Definition oneBitAdder : cava (Tuple2 Bit (Tuple2 Bit Bit)) (Tuple2 Bit Bit)
  := Rewire reorg1 ⟼ second Xor2 ⟼ Rewire reorg2 ⟼ (Xor2 ‖ Muxcy).


Definition oneBitAdder_top
  := (Input "cin" ‖ (Input "a" ‖ Input "b")) ⟼
     oneBitAdder ⟼
     ((Output "sum") ‖ (Output "cout")).

Definition forkBit (x : NetExpr Bit) : NetExpr (Tuple2 Bit Bit)
  := match x with
     | Net n => NetPair (Net n) (Net n)
     end.

Definition swapBit (x : NetExpr (Tuple2 Bit Bit)) : NetExpr (Tuple2 Bit Bit)
  := match x with
     | @NetPair Bit Bit x y => NetPair y x
     end.


Definition tupleLeft {a b c : signal} (x:NetExpr (Tuple2 a (Tuple2 b c))) :
                                      NetExpr (Tuple2 (Tuple2 a b) c)
   := match x with
      | NetPair p qr => match qr with
                          NetPair q r => NetPair (NetPair p q) r
                        end
      end.

