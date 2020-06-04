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
Local Open Scope string_scope.

From Coq Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

Require Import Cava.Monad.Cava.
Require Import Cava.Netlist.
Require Import Cava.Signal.
Require Import Cava.Types.

Definition NPeriphIn := 32.
Definition NPeriphOut := 32.
Definition NMioPads := 32.

Definition pinmuxInterface :=
  sequentialInterface "pinmux"
     "clk_i" PositiveEdge "rst_ni" NegativeEdge
     (mkPort "tl_i" (ExternalType "tlul_pkg::tl_h2d_t"),
      mkPort "periph_to_mio_i" (BitVec [NPeriphOut-1]),
      mkPort "periph_to_mio_oe_i" (BitVec [NPeriphOut-1]),
      mkPort "mio_in_i" (BitVec [NMioPads-1]))
     (mkPort "tl_o" (ExternalType "tlul_pkg::tl_d2h_t "),
      mkPort "mio_to_periph_o" (BitVec [NPeriphIn-1]),
      mkPort "mio_out_o" (BitVec [NMioPads-1]),
      mkPort "mio_oe_o" (BitVec [NMioPads-1]))
     [].

Definition pinmux {m bit} `{Cava m bit}
                  (inputs: string *
                           list bit *
                           list bit *
                           list bit) :
                  m (string *
                     list bit *
                     list bit *
                     list bit)%type :=
  let '(tl_i, periph_to_mio_i, periph_to_mio_oe_i, mio_in_i) := inputs in
  z <- zero ;;
  ret ("xxx", repeat z NPeriphIn, repeat z NMioPads, repeat z NMioPads).

(* Definition pinmux_netlist := makeNetlist pinmuxInterface pinmux. *)