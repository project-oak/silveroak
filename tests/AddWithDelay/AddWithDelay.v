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

From Coq Require Import NArith.NArith Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.

Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Lib.UnsignedAdders.

(******************************************************************************)
(* Add with delay                                                             *)
(******************************************************************************)

(*

The add-with-delay circuit takes the current 8-bit input (in) and the current
state value (on the wire labeled s), and adds them. After a one-cycle delay, the
sum is passed on to the [out] wire, and then after another delay it becomes the
new state. The adder is an 8-bit adder with no bit-growth i.e. it computes (a +
b) mod 256.
        _______
    ---| delay |------------
 s |   |_______|            |
   |   ___      _______     |
    --| + |----| delay |---------- out
 in --|___|    |_______|


Values at timestep t can be expressed in terms of previous values (assuming t > 2):

out(t) = in(t-1) + s(t-1)
s(t) = out(t-1) = in(t-2) + s(t-2)

Examples:

in  : 0 1 2 3 4 5 6  7  8
out : 0 0 1 2 4 6 9 12 16 20
s   : 0 0 0 1 2 4 6  9 12 16 20

in  : 1 1 1 1 1 1 1 1 1
out : 0 1 1 2 2 3 3 4 4 5
s   : 0 0 1 1 2 2 3 3 4 4 5

in  : 14 7 3 250
out :  0 14 7 17 1
s   :  0 0 14  7 17 1
*)

Section WithCava.
  Context {signal} {combsemantics: Cava signal}
          {semantics: CavaSeq combsemantics}.

  Definition addWithDelay : signal (Vec Bit 8) -> cava (signal (Vec Bit 8))
    := loopDelayS (addN >=> delay).
  
  (* A version to test loopDelaySR *)
  Definition addWithDelayAlt : signal (Vec Bit 8) -> cava (signal (Vec Bit 8))
    := loopDelaySRAlt (tupleInterfaceDefault [Vec Bit 8]) (addN >=> delay).

End WithCava.

(* Convenience notation for turning a list of nats into a list of 8-bit bitvectors *)
Local Notation "'#' l" := (map (fun i => N2Bv_sized 8 (N.of_nat i)) l)
                            (at level 40, only parsing).

Local Open Scope list_scope.

Example addWithDelay_ex1: sequential (addWithDelay (# [0;1;2;3;4;5;6;7;8])) = # [0;0;1;2;4;6;9;12;16;20].
Proof. reflexivity. Qed.

Example addWithDelay_ex2: sequential (addWithDelay (# [1;1;1;1;1;1;1;1;1])) = # [0;1;1;2;2;3;3;4;4;5].
Proof. reflexivity. Qed.

Example addWithDelay_ex3: sequential (addWithDelay (# [14; 7; 3; 250])) = # [0; 14; 7; 17; 1].
Proof. reflexivity. Qed.

(* Test the versions made with loopDelaySRAlt *)

Example addWithDelayAlt_ex1: sequential (addWithDelayAlt (# [0;1;2;3;4;5;6;7;8])) = # [0;0;1;2;4;6;9;12;16;20].
Proof. reflexivity. Qed.

Example addWithDelayAlt_ex2: sequential (addWithDelayAlt (# [1;1;1;1;1;1;1;1;1])) = # [0;1;1;2;2;3;3;4;4;5].
Proof. reflexivity. Qed.

Example addWithDelayAlt_ex3: sequential (addWithDelayAlt (# [14; 7; 3; 250])) = # [0; 14; 7; 17; 1].
Proof. reflexivity. Qed.