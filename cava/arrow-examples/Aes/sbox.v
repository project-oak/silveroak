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

From Coq Require Import Arith Eqdep_dec Vector Lia NArith Omega String Ndigits.
From Arrow Require Import Category Arrow.
From Cava Require Import Arrow.ArrowExport BitArithmetic.

From ArrowExamples Require Import Combinators Aes.pkg Aes.sbox_canright_pkg Aes.sbox_canright Aes.sbox_canright_masked_noreuse Aes.sbox_lut.

Section notation.
Import VectorNotations.
Import KappaNotation.
Open Scope kind_scope.

(* module aes_sbox #(
  parameter SBoxImpl = "lut"
) (
  input  aes_pkg::ciph_op_e op_i,
  input  logic [7:0]        data_i,
  output logic [7:0]        data_o
); *)
Program Definition aes_sbox
  (sbox_type: SboxImpl)
  :  <<Bit, Vector Bit 8, Unit>> ~> (Vector Bit 8) :=
  <[\ op_i data_i =>
      let data_o = !(
        match sbox_type with
        (* | SboxLut => aes_sbox_lut *)
        | SboxCanright => aes_sbox_canright
        (* | SboxCanrightMasked => sbox_canright_masked *)
        | SboxCanrightMaskedNoReuse =>

    (* // TODO: Use non-constant masks + remove corresponding comment in aes.sv.
    // See https://github.com/lowRISC/opentitan/issues/1005
    logic [7:0] in_data_m, out_data_m;
    logic [7:0] in_mask, out_mask;
    assign in_mask  = 8'hAA;
    assign out_mask = 8'h55; *)
          let inmask := <[ #255 ]> in
          let outmask := <[ #85 ]> in
          <[ \op_i data_i =>
            let masked_out = !aes_sbox_canright_masked_noreuse
                             op_i
                             (data_i ^ !inmask)
                             !inmask !outmask in
            masked_out ^ !outmask]>

        end
      ) op_i data_i
      in data_o
  ]>.
End notation.

Section regression_testing.
  Local Notation "# x" := (nat_to_bitvec_sized 8 x) (at level 99).

  (* Check equal at some random points *)
  Goal interp_combinational (aes_sbox_lut _) (false, #0)
    = interp_combinational (aes_sbox_canright _) (false, #0).
  Proof. vm_compute; auto.  Qed.

  (* TODO(blaxill): reduced bound for CI time *)
  Goal forall x, x < 10 ->
  interp_combinational (aes_sbox_lut _) (false, #x) = interp_combinational (aes_sbox_canright _) (false, #x).
  Proof. repeat (lia || destruct x); now vm_compute. Qed.

End regression_testing.

