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

Definition width := 32.
Definition NPeriphIn := width.
Definition NPeriphOut := width.
Definition NMioPads := width.

(* The SystemVerilog interface for the pinmux:

module pinmux (
  input                                         clk_i,
  input                                         rst_ni,
  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t                     tl_i,
  output tlul_pkg::tl_d2h_t                     tl_o,
  // Peripheral side
  input        [pinmux_reg_pkg::NPeriphOut-1:0] periph_to_mio_i,
  input        [pinmux_reg_pkg::NPeriphOut-1:0] periph_to_mio_oe_i,
  output logic [pinmux_reg_pkg::NPeriphIn-1:0]  mio_to_periph_o,
  // Pad side
  output logic [pinmux_reg_pkg::NMioPads-1:0]   mio_out_o,
  output logic [pinmux_reg_pkg::NMioPads-1:0]   mio_oe_o,
  input        [pinmux_reg_pkg::NMioPads-1:0]   mio_in_i
);
*)

Definition pinmuxInterface :=
  sequentialInterface "pinmux"
     "clk_i" NegativeEdge "rst_ni" NegativeEdge
     [mkPort "tl_i" (ExternalType "tlul_pkg::tl_h2d_t");
      mkPort "periph_to_mio_i" (Vec Bit NPeriphOut);
      mkPort "periph_to_mio_oe_i" (Vec Bit NPeriphOut);
      mkPort "mio_in_i" (Vec Bit NMioPads)]
     [mkPort "tl_o" (ExternalType "tlul_pkg::tl_d2h_t");
      mkPort "mio_to_periph_o" (Vec Bit NPeriphIn);
      mkPort "mio_out_o" (Vec Bit NMioPads);
      mkPort "mio_oe_o" (Vec Bit NMioPads)].


(* The SystemVerilog declaration for pinmux_reg_pkg::pinmux_reg2hw_t:

  typedef struct packed {
    logic [5:0]  q;
  } pinmux_reg2hw_periph_insel_mreg_t;

  typedef struct packed {
    pinmux_reg2hw_periph_insel_mreg_t [31:0] periph_insel; // [383:192]
    pinmux_reg2hw_mio_outsel_mreg_t [31:0] mio_outsel; // [191:0]
  } pinmux_reg2hw_t;
*)


Definition pinmux_reg2hw_t := ExternalType "pinmux_reg_pkg::pinmux_reg2hw_t".

Definition pinmux_reg_top_Interface :=
   sequentialInterface "pinmux_reg_top"
   "clk_i" PositiveEdge "rst_ni" NegativeEdge
   [mkPort "tl_i" (ExternalType "tlul_pkg::tl_h2d_t");
    mkPort "devmode_i" Bit]
   [mkPort "tl_o" (ExternalType "tlul_pkg::tl_d2h_t");
    mkPort "reg2hw" pinmux_reg2hw_t].

Definition pinmux_reg2hw_periph_insel_mreg_t
  := ExternalType "pinmux_reg2hw_periph_insel_mreg_t".

Definition kq (f: string)
              (reg2hw: Signal pinmux_reg2hw_t) (k: nat) : Signal (Vec Bit 6) :=
  let periph_insel : Signal (Vec (Vec Bit 6) NPeriphIn) :=
     SelectField (Vec (Vec Bit 6) NPeriphIn)
        reg2hw f in
  SelectField (Vec Bit 6) (IndexConst periph_insel k) "q".

Definition pinmux (inputs: Signal (ExternalType "tlul_pkg::tl_h2d_t") *
                           Signal (Vec Bit NPeriphOut)  *
                           Signal (Vec Bit NPeriphOut) *
                           Signal (Vec Bit NMioPads)) :
                    state CavaState
                     (Signal (ExternalType "tlul_pkg::tl_d2h_t") *
                     Signal (Vec Bit NMioPads) *
                     Signal (Vec Bit NPeriphIn) *
                     Signal (Vec Bit NMioPads)) :=
  let '(tl_i, periph_to_mio_i, periph_to_mio_oe_i, mio_in_i) := inputs in
  let const0 := Gnd in
  let const1 := Vcc in
  '(tl_o, reg2hw) <- blackBoxNet pinmux_reg_top_Interface (tl_i, const1) ;;
  (* Input Mux *)
  mio_in_i <- unpackVNet mio_in_i ;;
  let data_in_mux := VecLit ([const0; const1] ++ mio_in_i) in
  let mio_to_periph_o :=
    Vector.map (fun k => IndexAt data_in_mux (kq "periph_insel" reg2hw k))
               (vseq 0 NPeriphIn) in
  (* Output Mux *)
  periph_to_mio_i <- unpackVNet periph_to_mio_i ;;
  periph_to_mio_oe_i <- unpackVNet periph_to_mio_oe_i ;;
  let data_out_mux := VecLit ([const0; const1; const0] ++ periph_to_mio_i) in
  let oe_mux := VecLit ([const1; const1; const0] ++ periph_to_mio_oe_i) in
  let mio_out_o :=
    Vector.map (fun k => IndexAt data_out_mux (kq "mio_outsel" reg2hw k))
              (vseq 0 NPeriphIn) in
  let mio_oe_o :=
    Vector.map (fun k => IndexAt oe_mux (kq "mio_outsel" reg2hw k))
               (vseq 0 NPeriphIn) in
  mio_to_periph_o <- packVNet mio_to_periph_o ;;
  mio_out_o <- packVNet mio_out_o ;;
  mio_oe_o <- packVNet mio_oe_o ;;
  ret (tl_o,
       mio_to_periph_o,
       mio_out_o,
       mio_oe_o).

Definition pinmux_netlist := makeNetlist pinmuxInterface pinmux.
