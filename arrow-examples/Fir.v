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

From Cava Require Import Arrow.ArrowExport.
From Coq Require Import Lists.List NArith.NArith Strings.String Bool.Bvector.
Import ListNotations.

Local Open Scope string_scope.

Section notation.
  Import KappaNotation.
  Local Open Scope category_scope.
  Local Open Scope kind_scope.

  Local Notation Byte := (Vector Bit 8).

  Definition drop_last
    : << Vector Byte 4, Unit >> ~> Vector Byte 3 :=
    <[\input =>
      let '(init,_) = unsnoc input in
      init
      ]>.

  Definition coefficients
    : << Unit >> ~> Vector Byte 4 :=
    <[ {1,2,3,4} ]>.

  Definition adder
    : << Byte, Byte, Unit >> ~> Byte :=
    <[ \x y => x +% y ]>.

  Definition fir
    : << Byte, Unit >> ~> Byte :=
    <[ \byte =>
      letrec window = byte :: (!drop_last window) in
      (* TODO(#302): map2 adder should be mult, but we haven't added it yet *)
      !(foldl adder) #0 (!(map2 adder) window !coefficients)
    ]>.
End notation.

Open Scope kind_scope.

Require Import Cava.Types.
Require Import Cava.Netlist.

Local Notation Byte := (Signal.Vec Signal.Bit 8).
Definition fir_Interface :=
   sequentialInterface "fir" "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "in_stream" Byte] [mkPort "out_stream" Byte] [].

Definition fir_netlist :=
  build_netlist (closure_conversion fir) "fir" "in_stream" "out_stream".

Definition fir_tb_inputs : list (Bvector 8) :=
 map (N2Bv_sized 8) [1; 2; 3; 4; 5; 6; 7; 8; 9]%N.

Definition fir_tb_expected_outputs : list (Bvector 8) :=
  unroll_circuit_evaluation (closure_conversion fir) fir_tb_inputs.

Definition fir_tb :=
  testBench "fir_tb" fir_Interface
            fir_tb_inputs fir_tb_expected_outputs.

