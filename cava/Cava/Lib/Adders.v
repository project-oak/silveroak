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
Require Import Cava.Lib.CavaPrelude.
Require Import Cava.Lib.Combinators.
Require Import Cava.Util.Vector.

Section WithCava.
  Context `{semantics:Cava}.

  (* Build a half adder *)
  Definition halfAdder '(a, b) :=
    partial_sum <- xor2 (a, b) ;;
    carry <- and2 (a, b) ;;
    ret (partial_sum, carry).

  (* A full adder *)
  Definition fullAdder '(cin, (a, b))
                       : cava (signal Bit * signal Bit) :=
    '(abl, abh) <- halfAdder (a, b) ;;
    '(abcl, abch) <- halfAdder (abl, cin) ;;
    cout <- or2 (abh, abch) ;;
    ret (abcl, cout).

  (* Unsigned adder for n-bit vectors with carry bits both in and out *)
  Definition unsignedAdderV {n : nat}
            (inputs: signal Bit * (Vector.t (signal Bit * signal Bit)) n) :
            cava (Vector.t (signal Bit) n * signal Bit) :=
    colV fullAdder inputs.

  (* Adder with a pair of inputs of the same size and no bit-growth. *)
  Definition addN {n : nat}
            (ab: signal (Vec Bit n) * signal (Vec Bit n)) :
    cava (signal (Vec Bit n)) :=
    a <- unpackV (fst ab) ;;
    b <- unpackV (snd ab) ;;
    '(sum, _) <- unsignedAdderV (constant false, vcombine a b) ;;
    packV sum.

  Definition adderWithGrowthV {n : nat}
                              (inputs: signal Bit * (Vector.t (signal Bit * signal Bit)) n) :
                              cava (Vector.t (signal Bit) (n + 1)) :=
    '(sum, cout) <- unsignedAdderV inputs ;;
    ret (sum ++ [cout])%vector.

  Definition adderWithGrowthNoCarryInV {n : nat}
            (inputs: Vector.t (signal Bit * signal Bit) n) :
            cava (Vector.t (signal Bit) (n + 1)) :=
    adderWithGrowthV (constant false, inputs).

  Definition addLWithCinV {n : nat}
                          (cin : signal Bit)
                          (a b : Vector.t (signal Bit) n) :
                          cava (Vector.t (signal Bit) (n + 1)) :=
    adderWithGrowthV (cin, vcombine a b).

  (* Curried add with no carry in *)
  Definition addV {n : nat}
            (a b: Vector.t (signal Bit) n) :
            cava (Vector.t (signal Bit) (n + 1)) :=
    adderWithGrowthNoCarryInV (vcombine a b).

  (* A 3-input adder *)
  Definition adder_3input {aSize bSize cSize}
                          (a : signal (Vec Bit aSize))
                          (b : signal (Vec Bit bSize))
                          (c : signal (Vec Bit cSize)) :
                          cava (signal (Vec Bit (1 + max (1 + max aSize bSize) cSize)))
                          :=
    a_plus_b <- unsignedAdd (a, b) ;;
    sum <- unsignedAdd (a_plus_b, c) ;;
    ret sum.

  (* List version *)
  Definition unsignedAdderL (inputs: signal Bit * (list (signal Bit * signal Bit))) :
                            cava (list (signal Bit) * signal Bit) :=
    colL fullAdder inputs.

  Definition adderWithGrowthL (inputs: signal Bit * (list (signal Bit * signal Bit))) :
                              cava (list (signal Bit)) :=
    '(sum, cout) <- unsignedAdderL inputs ;;
    ret (sum ++ [cout])%list.

  Definition adderWithGrowthNoCarryInL
            (inputs: list (signal Bit * signal Bit)) :
            cava (list (signal Bit)) :=
    adderWithGrowthL (zero, inputs).

  Definition addLWithCinL (cin : signal Bit)
                          (a b : list (signal Bit)) :
                          cava (list (signal Bit)) :=
    adderWithGrowthL (cin, combine a b).

  Definition addL (a b : list (signal Bit)) :
                  cava (list (signal Bit)) :=
    adderWithGrowthNoCarryInL (combine a b).

  Section XilinxAdders.
    (* Build a full-adder with explicit use of Xilinx FPGA fast carry logic *)
    Definition xilinxFullAdder '(cin, (a, b))
    : cava (signal Bit * signal Bit) :=
      part_sum <- xor2 (a, b) ;;
      sum <- xorcy (part_sum, cin) ;;
      cout <- muxcy part_sum cin a  ;;
      ret (sum, cout).

    (* An unsigned adder built using the fast carry full-adder.*)
    Definition xilinxAdderWithCarry {n: nat}
               (cinab : signal Bit * (signal (Vec Bit n) * signal (Vec Bit n)))
      : cava (signal (Vec Bit n) * signal Bit)
      := let '(cin, (a, b)) := cinab in
         a0 <- unpackV a ;;
         b0 <- unpackV b ;;
         '(sum, cout) <- colV xilinxFullAdder (cin, vcombine a0 b0) ;;
         sum <- packV sum ;;
         ret (sum, cout).

    (* An unsigned adder with no bit-growth and no carry in *)
    Definition xilinxAdder {n: nat}
               (a b: signal (Vec Bit n))
      : cava (signal (Vec Bit n)) :=
      '(sum, carry) <- xilinxAdderWithCarry (constant false, (a, b)) ;;
      ret sum.
  End XilinxAdders.
End WithCava.
