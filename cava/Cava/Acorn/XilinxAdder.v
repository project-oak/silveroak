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

Require Import Coq.Bool.Bool.
Require Import Coq.NArith.NArith.

Require Import Coq.Vectors.Vector.
Import VectorNotations.

Require Import Coq.Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope type_scope.

Section WithCava.
  Context {signal} {m : Cava signal}.

  (****************************************************************************)
  (* Build a full-adder with explicit use of Xilinx FPGA fast carry logic     *)
  (****************************************************************************)

  Definition xilinxFullAdder '(cin, (a, b))
                             : cava (signal Bit * signal Bit) :=
    part_sum <- xor2 (a, b) ;;
    sum <- xorcy (part_sum, cin) ;;
    cout <- muxcy part_sum cin a  ;;
    ret (sum, cout).

  (******************************************************************************)
  (* An unsigned adder built using the fast carry full-adder.                   *)
  (******************************************************************************)

  Definition xilinxAdderWithCarry {n: nat}
              (cinab : signal Bit * (signal (Vec Bit n) * signal (Vec Bit n)))
            : cava (signal (Vec Bit n) * signal Bit)
    := let '(cin, (a, b)) := cinab in
      let a0 := peel a in
      let b0 := peel b in
      '(sum, cout) <- colV xilinxFullAdder (cin, vcombine a0 b0) ;;
      ret (unpeel sum, cout).

  (******************************************************************************)
  (* An unsigned adder with no bit-growth and no carry in                       *)
  (******************************************************************************)

  Definition xilinxAdder {n: nat}
              (a b: signal (Vec Bit n))
              : cava (signal (Vec Bit n)) :=
    '(sum, carry) <- xilinxAdderWithCarry (constant false, (a, b)) ;;
    ret sum.

End WithCava.

Section Withsemantics.

  (* A quick sanity check of the Xilinx adder with carry in and out *)
  Example xilinx_add_17_52:
    semantics (xilinxAdderWithCarry
                  ([false], ([N2Bv_sized 8 17], [N2Bv_sized 8 52]))) =
                  ([N2Bv_sized 8 69], [false]).
  Proof. vm_compute. reflexivity. Qed.

  (* A quick sanity check of the Xilinx adder with no bit-growth *)
  Example xilinx_no_growth_add_17_52:
    semantics (xilinxAdder [N2Bv_sized 8 17] [N2Bv_sized 8 52]) =
                  [N2Bv_sized 8 69].
  Proof. reflexivity. Qed.

  (* A proof that the the full-adder is correct. *)
  Lemma xilinxFullAdder_behaviour :
    forall (a : bool) (b : bool) (cin : bool),
          semantics (xilinxFullAdder ([cin], ([a], [b])))
          = ([xorb cin (xorb a b)],
             [(a && b) || (b && cin) || (a && cin)]).
  Proof.
    intros.
    unfold semantics.
    unfold fst.
    simpl.
    case a, b, cin.
    all : reflexivity.
  Qed.

End Withsemantics.
