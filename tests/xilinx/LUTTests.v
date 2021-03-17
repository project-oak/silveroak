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

Section WithCava.
  Context {signal} `{Cava signal}.

  Definition lut1_inv (i: signal Bit) : cava (signal Bit) :=
    o <- lut1 negb i ;;
    ret o.

  Definition lut2_and i0i1 : cava (signal Bit) :=
    o <- lut2 andb i0i1 ;;
    ret o.

  Definition lut3_mux '(s, i0, i1) : cava (signal Bit) :=
    o <- lut3 (fun s i0 i1 => if s then i1 else i0) (s, i0, i1) ;;
    ret o.

  Definition lut4_and i : cava (signal Bit) :=
  o <- lut4 (fun i0 i1 i2 i3 => andb (i0 && i1) (i2 && i3)) i ;;
  ret o.

  Definition lut5_and i : cava (signal Bit) :=
    o <- lut5 (fun i0 i1 i2 i3 i4 =>
              andb (andb (andb i0 i1) (andb i2 i3)) i4) i ;;
    ret o.

  Definition lut6_and i : cava (signal Bit) :=
    o <- lut6 (fun i0 i1 i2 i3 i4 i5 =>
              andb (andb (andb (andb i0 i1) (andb i2 i3)) i4) i5) i ;;
    ret o.

End WithCava.

(******************************************************************************)
(* LUT1 config test                                                           *)
(******************************************************************************)

  Definition lut1_inv_Interface
    := combinationalInterface "lut1_inv" [mkPort "a" Bit] [mkPort "b" Bit].

  Definition lut1_inv_netlist := makeNetlist lut1_inv_Interface lut1_inv.

  Definition lut1_inv_tb_inputs := [false; true].

  Definition lut1_inv_tb_expected_outputs : list bool :=
    simulate (Comb lut1_inv) lut1_inv_tb_inputs.

  Definition lut1_inv_tb :=
    testBench "lut1_inv_tb" lut1_inv_Interface
    lut1_inv_tb_inputs lut1_inv_tb_expected_outputs.

(****************************************************************************)
(* LUT2 config test                                                         *)
(****************************************************************************)

Definition lut2_and_Interface
  := combinationalInterface "lut2_and"
     [mkPort "a" Bit; mkPort "b" Bit]
     [mkPort "c" Bit].

Definition lut2_and_nelist := makeNetlist lut2_and_Interface lut2_and.

Definition lut2_and_tb_inputs : list (bool * bool) :=
 [(false, false); (false, true); (true, false); (true, true)].

Definition lut2_and_tb_expected_outputs : list bool :=
  simulate (Comb lut2_and) lut2_and_tb_inputs.

Definition lut2_and_tb :=
  testBench "lut2_and_tb" lut2_and_Interface
  lut2_and_tb_inputs lut2_and_tb_expected_outputs.

(****************************************************************************)
(* LUT3 config test                                                         *)
(****************************************************************************)

Definition lut3_mux_Interface
  := combinationalInterface "lut3_mux"
     [mkPort "s" Bit; mkPort "i0" Bit; mkPort "i1" Bit]
     [mkPort "o" Bit].

Definition lut3_mux_nelist := makeNetlist lut3_mux_Interface lut3_mux.

Definition lut3_mux_tb_inputs : list (bool * bool * bool) :=
 [(false, false, true);
  (false, true, false);
  (false, false, false);
  (true, false, true);
  (true, true, false);
  (true, true, true)].

Definition lut3_mux_tb_expected_outputs : list bool :=
  simulate (Comb lut3_mux) lut3_mux_tb_inputs.

Definition lut3_mux_tb :=
  testBench "lut3_mux_tb" lut3_mux_Interface
  lut3_mux_tb_inputs lut3_mux_tb_expected_outputs.

(****************************************************************************)
(* LUT4 config test                                                         *)
(****************************************************************************)

Definition lut4_and_Interface
  := combinationalInterface "lut4_and"
     [mkPort "i0" Bit;
      mkPort "i1" Bit;
      mkPort "i2" Bit;
      mkPort "i3" Bit]
     [mkPort "o" Bit].

Definition lut4_and_nelist := makeNetlist lut4_and_Interface lut4_and.

Definition lut4_and_tb_inputs : list (bool * bool * bool * bool) :=
 [(false, false, false, false);
  (true, true, true, true)].

Definition lut4_and_tb_expected_outputs : list bool :=
  simulate (Comb lut4_and) lut4_and_tb_inputs.

Definition lut4_and_tb :=
  testBench "lut4_and_tb" lut4_and_Interface
  lut4_and_tb_inputs lut4_and_tb_expected_outputs.

(****************************************************************************)
(* LUT5 config test                                                         *)
(****************************************************************************)

Definition lut5_and_Interface
  := combinationalInterface "lut5_and"
     [mkPort "i0" Bit;
      mkPort "i1" Bit;
      mkPort "i2" Bit;
      mkPort "i3" Bit;
      mkPort "i4" Bit]
     [mkPort "o" Bit].

Definition lut5_and_nelist := makeNetlist lut5_and_Interface lut5_and.

Definition lut5_and_tb_inputs : list (bool * bool * bool * bool * bool) :=
 [(false, false, false, false, false);
  (true, true, true, true, true)].

Definition lut5_and_tb_expected_outputs : list bool :=
  simulate (Comb lut5_and) lut5_and_tb_inputs.

Definition lut5_and_tb :=
  testBench "lut5_and_tb" lut5_and_Interface
  lut5_and_tb_inputs lut5_and_tb_expected_outputs.

(****************************************************************************)
(* LUT6 config test                                                         *)
(****************************************************************************)

Definition lut6_and_Interface
  := combinationalInterface "lut6_and"
     [mkPort "i0" Bit;
      mkPort "i1" Bit;
      mkPort "i2" Bit;
      mkPort "i3" Bit;
      mkPort "i4" Bit;
      mkPort "i5" Bit]
     [mkPort "o" Bit].

Definition lut6_and_nelist := makeNetlist lut6_and_Interface lut6_and.

Definition lut6_and_tb_inputs : list (bool * bool * bool * bool * bool * bool) :=
 [(false, false, false, false, false, false);
  (true, true, true, true, true, true)].


Definition lut6_and_tb_expected_outputs : list bool :=
  simulate (Comb lut6_and) lut6_and_tb_inputs.

Definition lut6_and_tb :=
  testBench "lut6_and_tb" lut6_and_Interface
  lut6_and_tb_inputs lut6_and_tb_expected_outputs.
