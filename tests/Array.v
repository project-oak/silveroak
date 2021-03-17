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
Local Open Scope vector_scope.

Section WithCava.
  Context `{Cava}.

  Definition array : cava (signal (Vec (Vec Bit 8) 4)) :=
    v <- Traversable.mapT (fun x => Vec.bitvec_literal (nat_to_bitvec_sized _ x)) [0;1;2;3] ;;
    packV v.

  Definition multiDimArray : cava (signal (Vec (Vec (Vec Bit 8) 4) 2)) :=
    arr1 <- array ;;
    arr2 <- array ;;
    packV [arr1; arr2].

  Definition arrayTest (i : signal (Vec Bit 8))
    : cava (signal (Vec Bit 8)) :=
    arr <- array ;;
    indexConst arr 0.

  Definition multiDimArrayTest (i : signal (Vec Bit 8))
    : cava (signal (Vec Bit 8)) :=
    arr <- multiDimArray ;;
    v <- indexConst arr 0 ;;
    indexConst v 0.

End WithCava.

Definition arrayTest_Interface
  := sequentialInterface "arrayTest"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "i" (Vec Bit 8)]
     [mkPort "o" (Vec Bit 8)].

Definition multiDimArrayTest_Interface
  := sequentialInterface "multiDimArrayTest"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "i" (Vec Bit 8)]
     [mkPort "o" (Vec Bit 8)].

Definition arrayTest_Netlist := makeNetlist arrayTest_Interface arrayTest.
Definition multiDimArrayTest_Netlist := makeNetlist multiDimArrayTest_Interface multiDimArrayTest.

Definition arrayTest_tb_inputs := List.repeat (nat_to_bitvec_sized 8 0) 2.

Definition arrayTest_tb_expected_outputs
  := simulate (Comb arrayTest) arrayTest_tb_inputs.
Definition multiDimArrayTest_tb_expected_outputs
  := simulate (Comb multiDimArrayTest) arrayTest_tb_inputs.

Definition arrayTest_tb
  := testBench "arrayTest_tb" arrayTest_Interface
      arrayTest_tb_inputs arrayTest_tb_expected_outputs.
Definition multiDimArrayTest_tb
  := testBench "multiDimArrayTest_tb" multiDimArrayTest_Interface
      arrayTest_tb_inputs multiDimArrayTest_tb_expected_outputs.
