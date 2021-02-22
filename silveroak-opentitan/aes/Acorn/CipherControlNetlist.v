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
Require Import ExtLib.Structures.Monads.
Import MonadNotation.

Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.
Require Import AcornAes.CipherControlCircuit.
Require Import AcornAes.SubBytesCircuit.
Require Import AcornAes.MixColumnsCircuit.
Require Import AcornAes.ShiftRowsCircuit.
Require Import AcornAes.AddRoundKeyCircuit.
Require Import AcornAes.Pkg.
Import Pkg.Notations.

Require Import AcornAes.ShiftRowsNetlist.
Require Import AcornAes.MixColumnsNetlist.

Definition cipher_state : SignalType := Pair (Pair key round_constant) state.

Definition aes_shift_rows' := instantiate aes_shift_rows_Interface (fun '(x,y) => aes_shift_rows x y).
Definition aes_mix_columns' := instantiate aes_mix_columns_Interface (fun '(x,y) => aes_shift_rows x y).

Definition key_expand_and_round
           (is_decrypt : Signal Bit)
           (round_key : Signal key)
           (rcon : Signal round_constant)
           (data : Signal state)
           (add_round_key_in_sel : Signal (Vec Bit 2))
           (round_key_sel : Signal Bit)
           (round_i : Signal round_index)
  : cava (Signal state) :=
  sub_bytes_out <- aes_sub_bytes' is_decrypt data ;;
  shift_rows_out <- aes_shift_rows' (is_decrypt, sub_bytes_out) ;;
  mix_columns_out <- aes_mix_columns' (is_decrypt, shift_rows_out) ;;

  (* Different rounds perform different operations on the state before adding
     the round key; select the appropriate wire based on add_round_key_in_sel *)
  let add_round_key_in :=
      mux4Tuple (mix_columns_out, data, shift_rows_out, mix_columns_out)
           add_round_key_in_sel in
  add_round_key_in <- localSignal add_round_key_in ;;

  (* Intermediate decryption rounds need to mix the key columns *)
  mixed_round_key <- inv_mix_columns_key round_key ;;

  key_to_add <- muxPair round_key_sel (round_key, mixed_round_key) ;;
  out <- aes_add_round_key key_to_add add_round_key_in ;;

  (* Key expansion *)
  '(round_key, rcon) <- key_expand is_decrypt round_i (round_key, rcon) ;;

  ret shift_rows_out.

Definition key_expand_and_round_Interface :=
  combinationalInterface "key_expand_and_round"
  [ mkPort "is_decrypt" Bit
  ; mkPort "key" key
  ; mkPort "rcon" round_constant
  ; mkPort "data" state
  ; mkPort "add_round_key_in_sel" (Vec Bit 2)
  ; mkPort "round_key_sel" Bit
  ; mkPort "round_i" (Vec Bit 4) ]
  [ mkPort "state_o" state ]
  [].

Definition key_expand_and_round_Netlist
  := makeNetlist key_expand_and_round_Interface
  (fun '(a, b, c, d, e, f, g ) => key_expand_and_round a b c d e f g).

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

(* Definition aes_cipher_core_simplified_Netlist *)
(*   := makeNetlist aes_cipher_core_simplified_Interface *)
(*   (fun '(op_i, in_valid_i, out_ready_i, key_init_i, state_init_i) => *)
(*     aes_cipher_core_simplified key_expand op_i in_valid_i out_ready_i key_init_i state_init_i). *)

