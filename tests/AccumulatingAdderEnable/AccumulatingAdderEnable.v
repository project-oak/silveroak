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
From Coq Require Import NArith.NArith Lists.List Vectors.Vector.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.

Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Lib.UnsignedAdders.
Import VectorNotations.
Local Open Scope vector_scope.

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
out    1  2  3  4  4  4  4  4

time   0  1  2  3  4  5  6  7
-----------------------------
valid  0  0  0  1  1  1  0  1
in     0  1  2  3  4  5  6  7
out    0  0  0  3  7 12 12 19

*)

Section WithCava.
  Context {signal} {combsemantics: Cava signal}.

  Definition mux2 {A} (sel : signal Bit) (f : signal A) (t : signal A)
    : cava (signal A) :=
    ret (pairSel sel (mkpair f t)).

  Definition accumulatingAdderEnable : signal (Pair (Vec Bit 8) Bit) -> cava (signal (Vec Bit 8))
    := loopDelayS (fun '(inp_and_valid, state) =>
                    let '(inp, valid) := unpair inp_and_valid in
                    (addN >=>
                     mux2 valid state) (inp, state)).

End WithCava.

(* Convenience notation for turning a list of nats into a list of bitvectors *)
Local Notation "'#' l" := (map (fun i => N2Bv_sized _ (N.of_nat i)) l)
                            (at level 40, only parsing).

Local Open Scope list_scope.

Example accumulatingAdderEnable_ex1:
  semantics (accumulatingAdderEnable
                (combine
                   (# [1;1;1;1;1;1;1;1])
                   (map nat2bool [1;1;1;1;0;0;0;0]))) = # [1;2;3;4;4;4;4;4].
Proof. reflexivity. Qed.

Example accumulatingAdderEnable_ex2:
  semantics (accumulatingAdderEnable
                (combine
                   (# [0;1;2;3;4;5;6;7])
                   (map nat2bool [0;0;0;1;1;1;0;1]))) = # [0;0;0;3;7;12;12;19].
Proof. reflexivity. Qed.

Definition accumulatingAdderEnable_Interface
  := sequentialInterface "accumulatingAdderEnable"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "en" Bit; mkPort "i" (Vec Bit 8)]
     [mkPort "o" (Vec Bit 8)]
     [].

Definition accumulatingAdderEnable_Netlist
  := makeNetlist accumulatingAdderEnable_Interface
                 (fun '(en, i) => accumulatingAdderEnable (mkpair i en)).

(* Now re-do the accumulating adder with enable using a loop with a delay with
   a clock-enable input. *)

Section WithCava.
  Context {signal} {combsemantics: Cava signal}.

  Definition accumulatingAdderEnable2 (en : signal Bit) :
                                       signal (Vec Bit 8) ->
                                       cava (signal (Vec Bit 8)) :=
    loopDelaySEnable en addN.


  Definition accumulatingAdderEnableTop (i_en : signal (Pair (Vec Bit 8) Bit))
                                        : cava (signal (Vec Bit 8)) :=
  let '(i, en) := unpair i_en in
  accumulatingAdderEnable2 en i.

End WithCava.

Example accumulatingAdderEnable2_ex1:
  semantics (accumulatingAdderEnableTop
                (combine
                   (# [1;1;1;1;1;1;1;1])
                   (map nat2bool [1;1;1;1;0;0;0;0]))) = # [1;2;3;4;4;4;4;4].
Proof. reflexivity. Qed.

Example accumulatingAdderEnable2_ex2:
  sequential (accumulatingAdderEnable2
                (map nat2bool [0;0;0;1;1;1;0;1])
                (# [0;1;2;3;4;5;6;7]) ) = # [0;0;0;3;7;12;12;19].
Proof. reflexivity. Qed.

Definition accumulatingAdderEnable2_Interface
  := sequentialInterface "accumulatingAdderEnable2"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "en" Bit; mkPort "i" (Vec Bit 8)]
     [mkPort "o" (Vec Bit 8)]
     [].

Definition accumulatingAdderEnable2_Netlist
  := makeNetlist accumulatingAdderEnable2_Interface
                 (fun '(en, i) => accumulatingAdderEnableTop (mkpair i en)).
