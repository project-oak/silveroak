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

Require Import Cava.Cava.

(******************************************************************************)
(* Accumulating adder with an enable.                                         *)
(******************************************************************************)

(*

The accumulating adder is similar to the countBy circuit, except that it also
takes a "valid" bit and ignores the input if this bit is false. For example:

          _______
      ---| delay |------------
     |   |_______|            |
     |           _____        |
     |----------|     |       |
     |   ___    | mux |------------- out
      --| + |---|_____|
   in --|___|      |
                   |
valid -------------'

Examples:

time   0  1  2  3  4  5  6  7
-----------------------------
valid  1  1  1  1  0  0  0  0
in     1  1  1  1  1  1  1  1
out    1  2  3  4  5  5  5  5

time   0  1  2  3  4  5  6  7
-----------------------------
valid  0  0  0  1  1  1  0  1
in     0  1  2  3  4  5  6  7
out    0  1  2  3  7 12 18 19

*)

Section WithCava.
  Context {signal} {semantics: Cava signal}.

  Definition accumulatingAdderEnable
    : Circuit (signal (Vec Bit 8) * signal Bit) (signal (Vec Bit 8))
    := LoopCE (Comb (addN >=> fork2)).

End WithCava.

(* Convenience notation for turning a list of nats into a list of bitvectors *)
Local Notation "'#' l" := (map (fun i => N2Bv_sized 8 (N.of_nat i)) l)
                            (at level 40, only parsing).

Example accumulatingAdderEnable_ex1:
  simulate accumulatingAdderEnable
            (combine
               (# [1;1;1;1;1;1;1;1])
               (map nat2bool [1;1;1;1;0;0;0;0])) = # [1;2;3;4;5;5;5;5].
Proof. reflexivity. Qed.

Example accumulatingAdderEnable_ex2:
  simulate accumulatingAdderEnable
            (combine
               (# [0;1;2;3;4;5;6;7])
               (map nat2bool [0;0;0;1;1;1;0;1])) = # [0;1;2;3;7;12;18;19].
Proof. reflexivity. Qed.

Definition accumulatingAdderEnable_Interface
  := sequentialInterface "accumulatingAdderEnable"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "i" (Vec Bit 8); mkPort "en" Bit]
     [mkPort "o" (Vec Bit 8)].

Definition accumulatingAdderEnable_Netlist
  := makeCircuitNetlist accumulatingAdderEnable_Interface accumulatingAdderEnable.
