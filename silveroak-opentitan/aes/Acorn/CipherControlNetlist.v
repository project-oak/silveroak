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

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Import ListNotations VectorNotations.

Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.
Require Import AcornAes.CipherControlCircuit.
Require Import AcornAes.Pkg.
Import Pkg.Notations.

Let cipher_state : SignalType := Pair (Pair key round_constant) state.

Definition key_expand_and_round_Interface :=
  combinationalInterface "key_expand_and_round"
  [ mkPort "is_decrypt" Bit
  ; mkPort "key_rcon_data" cipher_state
  ; mkPort "add_round_key_in_sel" (Vec Bit 2)
  ; mkPort "round_key_sel" Bit
  ; mkPort "round_i" (Vec Bit 4) ]
  [ mkPort "state_o" cipher_state ]
  [].

Definition key_expand_and_round_Netlist
  := makeNetlist key_expand_and_round_Interface
  (fun '(a, b, c, d, e ) => key_expand_and_round key_expand a b c d e).

Definition cipher_Interface :=
  combinationalInterface "cipher"
  [ mkPort "num_rounds_regular" (Vec Bit 4)
  ; mkPort "round_0" (Vec Bit 4)
  ; mkPort "is_decrypt" Bit
  ; mkPort "initial_key" key
  ; mkPort "initial_state" state
  ; mkPort "round_i" (Vec Bit 4) ]
  [ mkPort "state_o" state ]
  [].

Definition cipher_Netlist
  := makeNetlist cipher_Interface
  (fun '(num_rounds_regular, round_0, is_decrypt, initial_key, initial_state, round_i) =>
    cipher key_expand num_rounds_regular round_0 is_decrypt initial_key initial_state round_i).

Definition aes_cipher_core_simplified_Interface :=
  combinationalInterface "aes_cipher_core_simplified"
  [ mkPort "op_i" Bit
  ; mkPort "in_valid_i" Bit
  ; mkPort "out_ready_i" Bit
  ; mkPort "key_init_i" key
  ; mkPort "state_init_i" state ]
  [ mkPort "in_ready_o" Bit
  ; mkPort "out_valid_o" Bit
  ; mkPort "state_o" state ]
  [].

Definition aes_cipher_core_simplified_Netlist
  := makeNetlist aes_cipher_core_simplified_Interface
  (fun '(op_i, in_valid_i, out_ready_i, key_init_i, state_init_i) =>
    aes_cipher_core_simplified key_expand op_i in_valid_i out_ready_i key_init_i state_init_i).

