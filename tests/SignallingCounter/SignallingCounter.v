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
(* Signalling counter                                                         *)
(******************************************************************************)

(*

The signalling counter is similar to the countBy circuit, except that it also
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
  Context {signal} {combsemantics: Cava signal}
          {semantics: CavaSeq combsemantics} `{Monad cava}.

  Definition mux2 {A} (sel : signal Bit) (f : signal A) (t : signal A)
    : cava (signal A) :=
    ret (indexAt (unpeel [f; t]%vector) (unpeel ([sel]))).

  Definition signallingCounter : signal (Vec Bit 8) -> signal Bit -> cava (signal (Vec Bit 8))
    := fun inp valid =>
         let inp_and_valid : signal (Vec Bit 9) := unpeel (valid :: peel inp) in
         loopDelay (fun '(inp_and_valid, state) =>
                      let '(valid, inp) := uncons (peel inp_and_valid) in
                      (addN >=>
                       mux2 valid state >=>
                       fork2) (unpeel inp, state))
                   inp_and_valid.

End WithCava.

(* Convenience notation for turning a list of nats into a list of 8-bit bitvectors *)
Local Notation "'#' l" := (map (fun i => N2Bv_sized _ (N.of_nat i)) l)
                            (at level 40, only parsing).

Local Open Scope list_scope.

Example signallingCounter_ex1:
  sequential (signallingCounter
                (# [1;1;1;1;1;1;1;1])
                (map nat2bool [1;1;1;1;0;0;0;0])) = # [1;2;3;4;4;4;4;4].
Proof. reflexivity. Qed.

Example signallingCounter_ex2:
  sequential (signallingCounter
                (# [0;1;2;3;4;5;6;7])
                (map nat2bool [0;0;0;1;1;1;0;1])) = # [0;0;0;3;7;12;12;19].
Proof. reflexivity. Qed.

