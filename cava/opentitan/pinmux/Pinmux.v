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
Export MonadNotation.

From Coq Require Import Vector.
Import VectorNotations.

Open Scope monad_scope.

Require Import Cava.Cava.
Require Import Cava.Monad.CavaMonad.

Local Open Scope type_scope.

Definition NPeriphIn := 32.
Definition NPeriphOut := 32.
Definition NMioPads := 32.

Definition pinmuxInterface :=
  sequentialInterface "pinmux"
     "clk_i" PositiveEdge "rst_ni" NegativeEdge
     (mkPort "tl_i" (ExternalType "tlul_pkg::tl_h2d_t"),
      mkPort "periph_to_mio_i" (BitVec Bit NPeriphOut),
      mkPort "periph_to_mio_oe_i" (BitVec Bit NPeriphOut),
      mkPort "mio_in_i" (BitVec Bit NMioPads))
     (mkPort "tl_o" (ExternalType "tlul_pkg::tl_d2h_t"),
      mkPort "mio_to_periph_o" (BitVec Bit NPeriphIn),
      mkPort "mio_out_o" (BitVec Bit NMioPads),
      mkPort "mio_oe_o" (BitVec Bit NMioPads))
     [].

Definition pinmux_reg_top_Interface :=
   sequentialInterface "pinmux_reg_top"
   "clk_i" PositiveEdge "rst_ni" NegativeEdge
   (mkPort "tl_i" (ExternalType "tlul_pkg::tl_h2d_t"),
    mkPort "devmode_i" Bit)
   (mkPort "tl_o" (ExternalType "tlul_pkg::tl_d2h_t"),
    mkPort "reg2hw" (ExternalType "pinmux_reg_pkg::pinmux_reg2hw_t"))
   [].

Definition pinmux (inputs: Signal (ExternalType "tlul_pkg::tl_h2d_t") *
                           Vector.t (Signal Bit) NPeriphOut  *
                           Vector.t (Signal Bit) NPeriphOut *
                           Vector.t (Signal Bit) NMioPads) :
                   state CavaState (Signal (ExternalType "tlul_pkg::tl_d2h_t") *
                     Vector.t (Signal Bit) NPeriphIn *
                     Vector.t (Signal Bit) NMioPads *
                     Vector.t (Signal Bit) NMioPads) :=
  let '(tl_i, periph_to_mio_i, periph_to_mio_oe_i, mio_in_i) := inputs in
  const1 <- one ;;
  '(tl_o, reg2hw) <- blackBox pinmux_reg_top_Interface (tl_i, const1) ;;
  z <- zero ;;
  ret (tl_o,
       Vector.const z NPeriphIn,
       Vector.const z NMioPads,
       Vector.const z NMioPads).

Definition pinmux_netlist := makeNetlist pinmuxInterface pinmux.
