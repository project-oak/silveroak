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
(* Some handy test vectors                                                   *)
(******************************************************************************)

Definition bv4_0  := N2Bv_sized 4  0.
Definition bv4_1  := N2Bv_sized 4  1.
Definition bv4_2  := N2Bv_sized 4  2.
Definition bv4_3  := N2Bv_sized 4  3.
Definition bv4_15 := N2Bv_sized 4 15.

Definition bv5_0  := N2Bv_sized 5  0.
Definition bv5_3  := N2Bv_sized 5  3.
Definition bv5_16 := N2Bv_sized 5 16.
Definition bv5_30 := N2Bv_sized 5 30.

(******************************************************************************)
(* Test adders with no bit-growth and equal-sized inputs                      *)
(******************************************************************************)

(* Check 0 + 0 = 0 *)
Example add0_0 : addN (bv4_0, bv4_0) = bv4_0.
Proof. reflexivity. Qed.

(* Check 15 + 1 = 0 *)
Example add15_1 : addN (bv4_15, bv4_1) = bv4_0.
Proof. reflexivity. Qed.

Section WithCava.
  Context {signal} `{Cava signal}.

  (****************************************************************************)
  (* Unsigned addition with growth examples.                                  *)
  (****************************************************************************)

  Definition unsignedAddCircuit {m n : nat}
                                (ab : signal (Vec Bit m) * signal (Vec Bit n))
                                : cava (signal (Vec Bit (1 + max m n))) :=
    unsignedAdd (fst ab, snd ab).

  Definition adderGrowth {aSize bSize: nat}
                        (ab: signal (Vec Bit aSize) * signal (Vec Bit bSize)) :
                        cava (signal (Vec Bit (1 + max aSize bSize))) :=
    let (a, b) := ab in
    unsignedAddCircuit (a, b) .

  Definition add3InputTuple (aSize bSize cSize: nat)
                            (abc: signal (Vec Bit aSize) *
                                  signal (Vec Bit bSize)*
                                  signal (Vec Bit cSize)) :
                           cava (signal (Vec Bit (1 + max (1 + max aSize bSize) cSize))) :=
    let '(a, b, c) := abc in
    ab <- unsignedAdd (a, b) ;;
    unsignedAdd (ab, c).

End WithCava.

(* Check 0 + 0 = 0 *)
Example add5_0_0 : adderGrowth (bv4_0, bv4_0) = bv5_0.
Proof. reflexivity. Qed.

(* Check 1 + 2 = 3 *)
Example add5_1_2 : adderGrowth (bv4_1, bv4_2) = bv5_3.
Proof. reflexivity. Qed.

(* Check 15 + 1 = 16 *)
Example add5_15_1 : adderGrowth (bv4_15, bv4_1) = bv5_16.
Proof. reflexivity. Qed.

(* Check 15 + 15 = 30 *)
Example add5_15_15 : adderGrowth (bv4_15, bv4_15) = bv5_30.
Proof. reflexivity. Qed.

(******************************************************************************)
(* Generate a 4-bit unsigned adder with 5-bit output.                         *)
(******************************************************************************)

Definition adder4Interface
  := combinationalInterface "adder4"
     [mkPort "a" (Vec Bit 4); mkPort "b" (Vec Bit 4)]
     [mkPort "sum" (Vec Bit 5)].

Definition adder4Netlist
  := makeNetlist adder4Interface adderGrowth.

Definition adder4_tb_inputs
  := [(bv4_0, bv4_0); (bv4_1, bv4_2); (bv4_15, bv4_1); (bv4_15, bv4_15)].

Definition adder4_tb_expected_outputs
  := simulate (Comb unsignedAddCircuit) adder4_tb_inputs.

Definition adder4_tb
  := testBench "adder4_tb" adder4Interface
     adder4_tb_inputs adder4_tb_expected_outputs.

(******************************************************************************)
(* Generate a three input 8-bit unsigned adder with 10-bit output.            *)
(******************************************************************************)

Definition adder8_3inputInterface
  := combinationalInterface "adder8_3input"
     [mkPort "a" (Vec Bit 8); mkPort "b" (Vec Bit 8); mkPort "c" (Vec Bit 8)]
     [mkPort "sum" (Vec Bit 10)].

Definition adder8_3inputNetlist
  := makeNetlist adder8_3inputInterface (add3InputTuple 8 8 8).

Local Open Scope N_scope.

Definition adder8_3input_tb_inputs :=
  map (fun '(x, y, z) => (N2Bv_sized 8 x, N2Bv_sized 8 y, N2Bv_sized 8 z))
  [(17, 23, 95); (4, 200, 30); (255, 255, 200)].

Definition adder8_3input_tb_expected_outputs :=
  simulate (Comb (add3InputTuple 8 8 8)) adder8_3input_tb_inputs.

Definition adder8_3input_tb :=
  testBench "adder8_3input_tb" adder8_3inputInterface
  adder8_3input_tb_inputs adder8_3input_tb_expected_outputs.
