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

From Coq Require Import Bool.Bool.
From Coq Require Import Strings.Ascii Strings.String.
From Coq Require Import NArith.NArith.

From Coq Require Import Vectors.Vector.
Import VectorNotations.

From Coq Require Import Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Cava.
Require Import Cava.VectorUtils.
Require Import Cava.Monad.CavaMonad.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope type_scope.

(******************************************************************************)
(* Build a full-adder with explicit use of Xilinx FPGA fast carry logic       *)
(******************************************************************************)

Definition xilinxFullAdder {m bit} `{Cava m bit}
          (cin: bit)
          (ab: bit * bit)
  : m (bit * bit)%type :=
  let (a, b) := ab in
  part_sum <- xor2 (a, b) ;;
  sum <- xorcy (part_sum, cin) ;;
  cout <- muxcy part_sum cin a  ;;
  ret (sum, cout).

(* A proof that the the full-adder is correct. *)
Lemma xilinxFullAdder_behaviour :
  forall (a : bool) (b : bool) (cin : bool),
         combinational (xilinxFullAdder cin (a, b))
         = (xorb cin (xorb a b),
           (a && b) || (b && cin) || (a && cin)).
Proof.
  intros.
  unfold combinational.
  unfold fst.
  simpl.
  case a, b, cin.
  all : reflexivity.
Qed.

(******************************************************************************)
(* An unsigned adder built using the fast carry full-adder.                   *)
(******************************************************************************)

Definition xilinxAdderWithCarry {m bit} `{Cava m bit} {n: nat}
            (cinab : bit * (Vector.t bit n * Vector.t bit n))
           : m (Vector.t bit n * bit)
  := let '(cin, (a, b)) := cinab in
     '(sum, cout) <- colV n xilinxFullAdder cin (vcombine a b) ;;
     ret (sum, cout).

(* A quick sanity check of the Xilinx adder with carry in and out *)
Example xilinx_add_17_52:
  combinational (xilinxAdderWithCarry
                (false, (N2Bv_sized 8 17, N2Bv_sized 8 52))) =
                (N2Bv_sized 8 69, false).
Proof. reflexivity. Qed.

(******************************************************************************)
(* An unsigned adder with no bit-growth and no carry in                       *)
(******************************************************************************)

Definition xilinxAdder {m bit} `{Cava m bit} {n: nat}
            (a: Vector.t bit n) (b: Vector.t bit n)
           : m (Vector.t bit n) :=
  z <- zero ;;
  '(sum, carry) <- xilinxAdderWithCarry (z, (a, b)) ;;
  ret sum.

(* A quick sanity check of the Xilinx adder with no bit-growth *)
Example xilinx_no_growth_add_17_52:
  combinational (xilinxAdder (N2Bv_sized 8 17) (N2Bv_sized 8 52)) =
                 N2Bv_sized 8 69.
Proof. reflexivity. Qed.
