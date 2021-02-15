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

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Vectors.Vector.
Import VectorNotations.

Require Import ExtLib.Structures.Monads.
Import MonadNotation.

Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.Combinators.
Require Import AcornAes.Pkg.
Import Pkg.Notations.

Local Open Scope monad_scope.

Section WithCava.
  Context {signal} {semantics : Cava signal}.
  Context {round_index round_constant : SignalType}.

  Context (sub_bytes:     signal Bit -> signal state -> cava (signal state))
          (shift_rows:    signal Bit -> signal state -> cava (signal state))
          (mix_columns:   signal Bit -> signal state -> cava (signal state))
          (add_round_key: signal key -> signal state -> cava (signal state))
          (inv_mix_columns_key : signal key -> cava (signal key)).
  Context (key_expand : signal Bit -> signal round_index ->
                        (signal key  * signal round_constant) ->
                        cava (signal key * signal round_constant)).
  Local Infix "==?" := eqb (at level 40).
  Local Infix "**" := Pair (at level 40, left associativity).

  (* State of the AES cipher (key, round constant, AES state vector) *)
  Let cipher_state : SignalType := key ** round_constant ** state.
  (* The non-state signals that each round of the cipher loop needs access to *)
  Let cipher_signals : SignalType :=
    Bit (* op_i/is_decrypt : true for decryption, false for encryption *)
      ** round_index (* num_rounds_regular : round index of final round *)
      ** round_index (* round_0 : round index of first round *)
      ** cipher_state (* initial state, ignored for all rounds except first *)
      ** round_index (* current round_index *).

  Let cipher_control_state : SignalType :=
    Bit            (* idle *)
    ** Bit         (* generating decryption key *)
    ** round_index (* current round *)
    ** Bit         (* in_ready_o *)
    ** Bit         (* out_valid_o *)
    ** state       (* state_o *)
    ** Bit         (* out latch when not accepted *).

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

  Definition cipher_round
             (is_decrypt : signal Bit) (input: signal state) (key : signal key)
    : cava (signal state) :=
    (sub_bytes is_decrypt   >=>
     shift_rows is_decrypt  >=>
     mix_columns is_decrypt >=>
     add_round_key key) input.

  Definition key_expand_and_round
             (is_decrypt : signal Bit)
             (key_rcon_input : signal key * signal round_constant * signal state)
             (add_round_key_in_sel : signal (Vec Bit 2))
             (round_key_sel : signal Bit)
             (round_i : signal round_index)
    : cava (signal key * signal round_constant * signal state) :=
    let '(round_key, rcon, input) := key_rcon_input in
    shift_rows_out <- (sub_bytes is_decrypt >=> shift_rows is_decrypt) input ;;
    mix_columns_out <- mix_columns is_decrypt shift_rows_out ;;

    (* Different rounds perform different operations on the state before adding
       the round key; select the appropriate wire based on add_round_key_in_sel *)
    let add_round_key_in :=
        mux4 (mkpair (mkpair (mkpair mix_columns_out input) shift_rows_out) mix_columns_out)
             add_round_key_in_sel in

    (* Intermediate decryption rounds need to mix the key columns *)
    mixed_round_key <- inv_mix_columns_key round_key ;;

    out <- add_round_key (pairSel round_key_sel (mkpair round_key mixed_round_key))
                        add_round_key_in ;;

    (* Key expansion *)
    '(round_key, rcon) <- key_expand is_decrypt round_i (round_key, rcon) ;;

    ret (round_key, rcon, out).

  Definition cipher_step
             (num_rounds_regular round_0 : signal (round_index))
             (is_decrypt : signal Bit) (* called op_i in OpenTitan *)
             (key_rcon_data : signal key * signal round_constant * signal state)
             (round_i : signal round_index)
    : cava (signal key * signal round_constant * signal state) :=
    let '(round_key, rcon, input) := key_rcon_data in
    is_first_round <- round_i ==? round_0 ;;
    is_final_round <- round_i ==? num_rounds_regular ;;
    (* add_round_key_in_sel :
       1 if round_i = 0, 2 if round_i = num_rounds_regular, 0 otherwise *)
    let add_round_key_in_sel := unpeel [is_first_round; is_final_round]%vector in
    is_middle_round <- nor2 (is_first_round, is_final_round) ;;
    (* round_key_sel : 1 for a decryption middle round, 0 otherwise *)
    round_key_sel <- and2 (is_middle_round, is_decrypt) ;;
    key_expand_and_round is_decrypt (round_key, rcon, input)
                         add_round_key_in_sel round_key_sel round_i.

  Definition cipher
             (num_rounds_regular round_0 : signal (round_index))
             (is_decrypt : signal Bit) (* called op_i in OpenTitan *)
             (initial_key : signal key) (initial_rcon : signal round_constant)
             (round_indices : list (signal round_index)) (input : signal state)
    : cava (signal state) :=
    '(_, _, out) <- foldLM (cipher_step num_rounds_regular round_0 is_decrypt) round_indices
                          (initial_key, initial_rcon, input) ;;
    ret out.

  Definition cipher_inner_loop
             (input_and_state : signal cipher_signals * signal cipher_state)
    : cava (signal cipher_state) :=
    let '(input, feedback_state) := input_and_state in
    let '(is_decrypt, num_rounds_regular, round_0, initial_state, idx) := unpacked_signal input in
    is_first_round <- idx ==? round_0 ;;
    cipher_state' <- muxPair is_first_round (initial_state, feedback_state) ;;
    let '(k, round, st) := unpacked_signal cipher_state' in
    '(k, round, st) <- cipher_step num_rounds_regular round_0 is_decrypt
                                   (k, round, st) idx ;;
    ret (packed_signal cipher_state (k, round, st)).

  Context {seqsemantics : CavaSeq semantics}.
  Context (initial_rcon_forward: signal round_constant). (* #1 *)
  Context (initial_rcon_backward: signal round_constant). (* #64 *)

  Definition cipher_new
             (num_rounds_regular round_0 : signal (round_index))
             (is_decrypt : signal Bit) (* called op_i in OpenTitan *)
             (initial_key : signal key)
             (round_i : signal round_index) (input : signal state)
    : cava (signal state) :=
    initial_rcon <- muxPair is_decrypt (initial_rcon_forward, initial_rcon_backward) ;;
    let initial_state := mkpair (mkpair initial_key initial_rcon) input in
    (* join all signals that are needed inside the cipher loop *)
    let loop_input := packed_signal cipher_signals
      (is_decrypt, num_rounds_regular, round_0, initial_state, round_i) in
    loop_out <- loopDelayS cipher_inner_loop loop_input ;;
    let '(_, final_data) := unpair loop_out in
    ret final_data.

  Context (num_rounds_regular round_0 round_1 round_final: signal (round_index)).
  Context (inc_round: signal round_index -> cava (signal round_index)).

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
      (fun '((inputs, st) : signal (Pair Bit Bit)  * signal cipher_control_state) =>

        (* unpack inputs and state from Cava 'Pair's *)
        let '(in_valid_i, out_valid_i) := unpair inputs in
        let '(last_idle, last_gen_dec_key, last_round, _, _, last_buffered_state, last_output_latch)
          := unpacked_signal st in

        (* Are we still processing an input (or generating a decryption key) *)
        is_final_round <- last_round ==? round_final ;;
        is_finishing <- and2 (is_final_round, last_gen_dec_key) ;;
        becoming_idle <- or2 (last_idle, is_finishing) ;;
        inv_last_idle <- inv last_idle ;;
        (* If we weren't idle and we are about to finish,
        * we must be producing a new result *)
        producing_output <- and2 (inv_last_idle, is_finishing) ;;
        (* Accept input if we are not busy next cycle *)
        accepted_input <- and2 (becoming_idle, in_valid_i) ;;
        (* We are only truly idle if there was no incoming input *)
        inv_in_valid_i <- inv in_valid_i ;;
        idle <- and2 (becoming_idle, inv_in_valid_i) ;;

        (* Are we generating decryption key?
        * Decryption requires a full pass to generate decryption key
        * Currently not implemented/supported *)
        let generating_decryption_key := constant false in

        (* Update round, hold at 0 if idle. This is correct when accepting input
        * as acceptance requires becoming_idle is true *)
        next_round <- inc_round last_round ;;
        round <- muxPair becoming_idle (round_0, next_round) ;;

        (* we only need to grab the state at the last round *)
        st <- cipher_new round_final round_0 is_decrypt initial_key round initial_state ;;
        buffered_state <- muxPair producing_output (st, last_buffered_state) ;;

        out_valid_o <- or2 (last_output_latch, producing_output) ;;
        inv_out_valid_i <- inv out_valid_i ;;
        output_latch <- and2 (out_valid_o, inv_out_valid_i) ;;

        ret (packed_signal cipher_control_state
          ( idle
          , generating_decryption_key
          , round
          , becoming_idle
          , out_valid_o
          , buffered_state
          , output_latch
          ))
      ) (mkpair in_valid_i out_ready_i) ;;

    let '(_, _, _, in_ready_o, out_valid_o, state_o, _) := unpacked_signal st in
    ret (in_ready_o, out_valid_o, state_o).

End WithCava.
