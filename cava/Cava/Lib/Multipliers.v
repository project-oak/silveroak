(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
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

Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Require Import ExtLib.Structures.Monads.
Import ListNotations VectorNotations MonadNotation.
Open Scope monad_scope.

Require Import Cava.Core.Core.
Require Import Cava.Lib.Adders.
Require Import Cava.Lib.CavaPrelude.
Require Import Cava.Lib.Combinators.
Require Import Cava.Lib.Multiplexers.
Require Import Cava.Util.Vector.
Import Circuit.Notations.

(**** IMPORTANT: if you make changes to the API of these definitions, or add new
      ones, make sure you update the reference at docs/reference.md! ****)

Section WithCava.
  Context `{semantics:Cava}.

  (* square(x):
       if x == 0:
         return 0
       y = x // 2
       r = square(y)
       if x is even:
         return r * 4
       else:
         return r * 4 + y * 4 + 1
  *)

  (* square an n-bit little-endian bitvector *)
  Fixpoint squareN {n}
    : signal (Vec Bit n) -> cava (signal (Vec Bit n)) :=
    match n as n return signal (Vec Bit n) -> cava (signal (Vec Bit n)) with
    | O => ret
    | S n' =>
      fun x =>
        (* get bits 1..n of the input *)
        y <- Vec.tl x ;;
        (* recursively square bits 1..n *)
        r <- squareN y ;;
        (* multiply by 4 and truncate to n bits *)
        r_times4 <- (Vec.cons zero >=> Vec.cons zero >=> Vec.shiftout) r ;;
        (* multiply by 4 and truncate to n bits *)
        y_times4 <- (Vec.cons zero >=> Vec.cons zero >=> Vec.shiftout) y ;;
        (* compute the expression for the odd case (r*4+y*4+1) *)
        y_times4_plus1 <- incrN y_times4 ;;
        odd_case <- addN (r_times4, y_times4_plus1) ;;
        (* based on bit 0 of input, select the odd or even case *)
        x0 <- Vec.hd x ;;
        mux2 x0 (r_times4, odd_case)
    end.
End WithCava.
