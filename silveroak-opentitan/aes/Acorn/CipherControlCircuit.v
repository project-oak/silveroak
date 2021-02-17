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

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Vectors.Vector.
Import VectorNotations.

Require Import ExtLib.Structures.Monads.
Import MonadNotation.

Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.Combinators.
Require Import AcornAes.Pkg.
Require Import AcornAes.SubBytesCircuit.
Require Import AcornAes.AddRoundKeyCircuit.
Require Import AcornAes.ShiftRowsCircuit.
Require Import AcornAes.MixColumnsCircuit.
Require Import AcornAes.Cipher.
Import Pkg.Notations.

Local Open Scope monad_scope.
Local Open Scope vector_scope.

Notation round_index := (Vec Bit 4) (only parsing).
Notation round_constant := (Vec Bit 8) (only parsing).

Section WithCava.
  Context {signal} {semantics : Cava signal}.
  Context {seqsemantics : CavaSeq semantics}.

  Context (key_expand : signal Bit -> signal round_index ->
                        (signal key  * signal round_constant) ->
                        cava (signal key * signal round_constant)).

  Definition rcon_fwd: signal round_constant :=
    unpeel (Vector.map constant (nat_to_bitvec_sized _ 1)).
  Definition rcon_bwd: signal round_constant :=
    unpeel (Vector.map constant (nat_to_bitvec_sized _ 64)).

  Definition initial_rcon (is_decrypt: signal Bit): cava (signal round_constant) :=
    muxPair is_decrypt (rcon_bwd, rcon_fwd).

  Definition round_0: signal round_index :=
    unpeel (Vector.map constant (nat_to_bitvec_sized _ 0)).
  Definition round_final: signal round_index :=
    unpeel (Vector.map constant (nat_to_bitvec_sized _ 13)).

  Definition round_1: signal round_index :=
    unpeel (Vector.map constant (nat_to_bitvec_sized _ 1)).

  Definition inc_round (current: signal round_index): cava (signal round_index) :=
    let sum := (@unsignedAdd _ _ 4 4 (current, round_1)) in
    ret (unpeel (Vector.tl (peel sum))).

  Local Infix "==?" := eqb (at level 40).
  Local Infix "**" := Pair (at level 40, left associativity).

  Let cipher_control_state : SignalType :=
    Bit            (* idle *)
    ** Bit         (* generating decryption key *)
    ** round_index (* current round *)
    ** Bit         (* in_ready_o *)
    ** Bit         (* out_valid_o *)
    ** state       (* state_o *)
    ** Bit         (* out latch when not accepted *).

  Let cipher_control_signals :=
    Bit (* is_decrypt *)
    ** Bit (* in_valid_i *)
    ** Bit (* out_ready_i *)
    ** key (* initial_key *)
    ** state (* initial_state *).

  Section Packing.
    Fixpoint unpacked_left_type A: Type :=
      match A with
      | Pair a b => unpacked_left_type a * signal b
      | x => signal x
      end.

    Fixpoint unpacked_signal {A}: signal A -> unpacked_left_type A :=
      match A as A return signal A -> unpacked_left_type A with
      | Pair a b => fun x =>
        let '(y,z) := unpair x in
        (unpacked_signal y, z)
      | _ => fun x => x
      end.

    Fixpoint packed_signal A: unpacked_left_type A -> signal A :=
      match A with
      | Pair a b => fun '(x,y) =>
        mkpair (packed_signal _ x) y
      | _ => fun x => x
      end.
  End Packing.

  Definition inv_mix_columns_key := aes_mix_columns (constant true).

  (* Plug in our concrete components to the skeleton in Cipher.v *)
  Definition cipher := cipher
    (round_index:=round_index) (round_constant:=round_constant)
    aes_sub_bytes aes_shift_rows aes_mix_columns aes_add_round_key
    inv_mix_columns_key key_expand initial_rcon.

  (* Comparable to OpenTitan aes_cipher_core but with simplified signalling *)
  Definition aes_cipher_core_simplified
    (is_decrypt: signal Bit)
    (in_valid_i out_ready_i: signal Bit)
    (initial_key: signal key)
    (initial_state: signal state)
    : cava
    ( signal Bit (* in_ready_o *)
    * signal Bit (* out_valid_o *)
    * signal state (* state_o *)
    ) :=
    st <- loopDelayS
    (* state and key buffers are handled by `cipher_new` so we don't explicitly
    * register them here. There is an additional state buffer here for storing the output
    * until it is accepted via out_ready_i. *)
      (fun '((inputs, st) : signal cipher_control_signals * signal cipher_control_state) =>

        (* unpack inputs and state from Cava 'Pair's *)
        let '(is_decrypt, in_valid_i, out_ready_i, initial_key, initial_state)
          := unpacked_signal inputs in
        let '(last_idle, last_gen_dec_key, last_round, _, _, last_buffered_state, last_output_latch)
          := unpacked_signal st in

        (* Are we still processing an input (or generating a decryption key) *)
        is_final_round <- last_round ==? round_final ;;
        inv_last_gen_dec_key <- inv last_gen_dec_key ;;
        is_finishing <- and2 (is_final_round, inv_last_gen_dec_key) ;;
        becoming_idle <- or2 (last_idle, is_finishing) ;;
        inv_last_idle <- inv last_idle ;;
        (* If we weren't idle and we are about to finish,
        * we must be producing a new result *)
        producing_output <- and2 (inv_last_idle, is_finishing) ;;
        (* Accept input if we are not busy next cycle *)
        accepted_input <- and2 (becoming_idle, in_valid_i) ;;
        (* Are we generating decryption key?
        * Decryption requires a full pass to generate decryption key *)
        generating_decryption_key <- and2 (accepted_input, is_decrypt) ;;
        (* We are only truly idle if there was no incoming input *)
        inv_in_valid_i <- inv in_valid_i ;;
        idle <- and2 (becoming_idle, inv_in_valid_i) ;;

        (* Update round, hold at 0 if idle. This is correct when accepting input
        * as acceptance requires becoming_idle is true *)
        next_round <- inc_round last_round ;;
        next_round <- muxPair is_final_round (round_0, next_round) ;;
        round <- muxPair becoming_idle (round_0, next_round) ;;

        (* we only need to grab the state at the last round *)
        st <- cipher round_final round_0 generating_decryption_key initial_key initial_state round ;;
        buffered_state <- muxPair producing_output (st, last_buffered_state) ;;

        out_valid_o <- or2 (last_output_latch, producing_output) ;;
        inv_out_ready_i <- inv out_ready_i ;;
        output_latch <- and2 (out_valid_o, inv_out_ready_i) ;;

        ret (packed_signal cipher_control_state
          ( idle
          , generating_decryption_key
          , round
          , becoming_idle
          , out_valid_o
          , buffered_state
          , output_latch
          ))
      )
      (packed_signal cipher_control_signals
        (is_decrypt, in_valid_i, out_ready_i, initial_key, initial_state)) ;;

    let '(_, _, _, in_ready_o, out_valid_o, state_o, _) := unpacked_signal st in
    ret (in_ready_o, out_valid_o, state_o).

End WithCava.

(* Interface of existing aes_key_expand
* https://github.com/lowRISC/opentitan/blob/783edaf444eb0d9eaf9df71c785089bffcda574e/hw/ip/aes/rtl/aes_key_expand.sv *)
Definition aes_key_expand_Interface :=
   sequentialInterface "aes_key_expand"
   "clk_i" PositiveEdge "rst_ni" NegativeEdge
   [ mkPort "op_i" Bit
   ; mkPort "step_i" Bit
   ; mkPort "clear_i" Bit
   ; mkPort "round_i" (Vec Bit 4)
   ; mkPort "key_len_i" (Vec Bit 3)
   ; mkPort "key_i" key
   ]
   [ mkPort "key_o" key ]
   [].

(* TODO(blaxill): our key_expand interface is simpler but also assumes rcon is
* passed (rather than internally registered), change back to OT version or provide
  a key_expand implementation ? *)
Definition key_expand
    (op_i: Signal Bit) (round: Signal round_index)
    (key_rcon: Signal key * Signal round_constant):
               cava (Signal key * Signal round_constant) :=
  let '(k, _) := key_rcon in
  let clear := constant false in
  key_o <- blackBoxNet aes_key_expand_Interface
    (op_i, constant true, clear, round, unpeel (Vector.map constant [true;false;false]), k) ;;
  ret (key_o, rcon_fwd).

