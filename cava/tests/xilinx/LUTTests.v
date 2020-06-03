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

From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Monad.Cava.
Require Import Cava.Netlist.
Require Import Cava.Types.

Local Open Scope list_scope.
Local Open Scope monad_scope.
Local Open Scope string_scope.

(****************************************************************************)
(* LUT1 config test                                                         *)
(****************************************************************************)

Definition lut1_inv {m bit} `{Cava m bit} (i: bit) : m bit :=
  o <- lut1 negb i ;;
  ret o.

Definition lut1_inv_Interface
  := mkCombinationalInterface "lut1_inv" (One ("a", Bit)) (One ("b", Bit)) [].

Definition lut1_inv_netlist := makeNetlist lut1_inv_Interface lut1_inv.

Definition lut1_inv_tb_inputs := [false; true].

Definition lut1_inv_tb_expected_outputs : list bool :=
  map (fun i => combinational (lut1_inv i)) lut1_inv_tb_inputs.

Definition lut1_inv_tb :=
  testBench "lut1_inv_tb" lut1_inv_Interface
  lut1_inv_tb_inputs lut1_inv_tb_expected_outputs.

(****************************************************************************)
(* LUT2 config test                                                         *)
(****************************************************************************)

Definition lut2_and {m bit} `{Cava m bit} (i0i1 : bit * bit) : m bit :=
  o <- lut2 andb i0i1 ;;
  ret o.

Definition lut2_and_Interface
  := mkCombinationalInterface "lut2_and"
     (Tuple2 (One ("a", Bit)) (One ("b", Bit)))
     (One ("c", Bit))
     [].

Definition lut2_and_nelist := makeNetlist lut2_and_Interface lut2_and.

Definition lut2_and_tb_inputs : list (bool * bool) :=
 [(false, false); (false, true); (true, false); (true, true)].       

 Definition lut2_and_tb_expected_outputs : list bool :=
  map (fun i => combinational (lut2_and i)) lut2_and_tb_inputs.

Definition lut2_and_tb :=
  testBench "lut2_and_tb" lut2_and_Interface
  lut2_and_tb_inputs lut2_and_tb_expected_outputs.

(****************************************************************************)
(* LUT3 config test                                                         *)
(****************************************************************************)

Definition lut3_mux {m bit} `{Cava m bit}
           (si0i1 : bit * (bit * bit)) : m bit :=
  let '(s, (i0, i1)) := si0i1 in
  o <- lut3 (fun s i0 i1 => if s then i1 else i0) (s, i0, i1) ;;
  ret o.

Definition lut3_mux_Interface
  := mkCombinationalInterface "lut3_mux"
     (Tuple2 (One ("s", Bit))
             (Tuple2 (One ("i0", Bit)) (One ("i1", Bit))))
     (One ("o", Bit))
     [].

Definition lut3_mux_nelist := makeNetlist lut3_mux_Interface lut3_mux.

Definition lut3_mux_tb_inputs : list (bool * (bool * bool)) :=
 [(false, (false, true));
  (false, (true, false));
  (false, (false, false));
  (true, (false, true));
  (true, (true, false));
  (true, (true, true))].

 Definition lut3_mux_tb_expected_outputs : list bool :=
  map (fun i => combinational (lut3_mux i)) lut3_mux_tb_inputs.

Definition lut3_mux_tb :=
  testBench "lut3_mux_tb" lut3_mux_Interface
  lut3_mux_tb_inputs lut3_mux_tb_expected_outputs.

(****************************************************************************)
(* LUT4 config test                                                         *)
(****************************************************************************)

Definition lut4_and {m bit} `{Cava m bit}
           (i : bit * bit * bit * bit) : m bit :=
  let '(i0, i1, i2, i3) := i in
  o <- lut4 (fun i0 i1 i2 i3 =>
            andb (andb i0 i1) (andb i2 i3)) i ;;
  ret o.

(* The left-associative nesting we need to use here is mad. We need to
   find a better way. Satnam.
*)
Definition lut4_and_Interface
  := mkCombinationalInterface "lut4_and"
     (Tuple2 (Tuple2 (Tuple2 (One ("i0", Bit)) (One ("i1", Bit))) 
                     (One ("i2", Bit)))
             (One ("i3", Bit))
     )
     (One ("o", Bit))
     [].

Definition lut4_and_nelist := makeNetlist lut4_and_Interface lut4_and.

Definition lut4_and_tb_inputs : list (bool * bool * bool * bool) :=
 [(false, false, false, false);
  (true, true, true, true)].

Definition lut4_and_tb_expected_outputs : list bool :=
  map (fun i => combinational (lut4_and i)) lut4_and_tb_inputs.

Definition lut4_and_tb :=
  testBench "lut4_and_tb" lut4_and_Interface
  lut4_and_tb_inputs lut4_and_tb_expected_outputs.

(****************************************************************************)
(* LUT5 config test                                                         *)
(****************************************************************************)

Definition lut5_and {m bit} `{Cava m bit}
           (i : bit * bit * bit * bit * bit) : m bit :=
  let '(i0, i1, i2, i3, i4) := i in
  o <- lut5 (fun i0 i1 i2 i3 i4 =>
            andb (andb (andb i0 i1) (andb i2 i3)) i4) i ;;
  ret o.

(* The left-associative nesting we need to use here is mad. We need to
   find a better way. Satnam.
*)
Definition lut5_and_Interface
  := mkCombinationalInterface "lut5_and"
     (Tuple2 (Tuple2 (Tuple2 (Tuple2 (One ("i0", Bit)) (One ("i1", Bit))) 
                     (One ("i2", Bit)))
             (One ("i3", Bit))) (One ("i4", Bit))
     )
     (One ("o", Bit))
     [].

Definition lut5_and_nelist := makeNetlist lut5_and_Interface lut5_and.

Definition lut5_and_tb_inputs : list (bool * bool * bool * bool * bool) :=
 [(false, false, false, false, false);
  (true, true, true, true, true)].

Definition lut5_and_tb_expected_outputs : list bool :=
  map (fun i => combinational (lut5_and i)) lut5_and_tb_inputs.

Definition lut5_and_tb :=
  testBench "lut5_and_tb" lut5_and_Interface
  lut5_and_tb_inputs lut5_and_tb_expected_outputs.

(****************************************************************************)
(* LUT6 config test                                                         *)
(****************************************************************************)

Definition lut6_and {m bit} `{Cava m bit}
           (i : bit * bit * bit * bit * bit * bit) : m bit :=
  let '(i0, i1, i2, i3, i4, i5) := i in
  o <- lut6 (fun i0 i1 i2 i3 i4 i5 =>
            andb (andb (andb (andb i0 i1) (andb i2 i3)) i4) i5) i ;;
  ret o.

(* The left-associative nesting we need to use here is mad. We need to
   find a better way. Satnam.
*)
Definition lut6_and_Interface
  := mkCombinationalInterface "lut6_and"
     (Tuple2 (Tuple2 (Tuple2 (Tuple2 (Tuple2 (One ("i0", Bit)) (One ("i1", Bit))) 
                     (One ("i2", Bit)))
             (One ("i3", Bit))) (One ("i4", Bit))) (One ("i5", Bit))
     )
     (One ("o", Bit))
     [].

Definition lut6_and_nelist := makeNetlist lut6_and_Interface lut6_and.

Definition lut6_and_tb_inputs : list (bool * bool * bool * bool * bool * bool) :=
 [(false, false, false, false, false, false);
  (true, true, true, true, true, true)].

Definition lut6_and_tb_expected_outputs : list bool :=
  map (fun i => combinational (lut6_and i)) lut6_and_tb_inputs.

Definition lut6_and_tb :=
  testBench "lut6_and_tb" lut6_and_Interface
  lut6_and_tb_inputs lut6_and_tb_expected_outputs.   