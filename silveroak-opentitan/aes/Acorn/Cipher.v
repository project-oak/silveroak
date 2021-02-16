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
  Context {signal} {semantics : Cava signal} {seqsemantics : CavaSeq semantics}.
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

  Definition key_expand_and_round
             (is_decrypt : signal Bit)
             (key_rcon_data : signal cipher_state)
             (add_round_key_in_sel : signal (Vec Bit 2))
             (round_key_sel : signal Bit)
             (round_i : signal round_index)
    : cava (signal cipher_state) :=
    let '(key_rcon, data) := unpair key_rcon_data in
    let '(round_key, rcon) := unpair key_rcon in
    shift_rows_out <- (sub_bytes is_decrypt >=> shift_rows is_decrypt) data ;;
    mix_columns_out <- mix_columns is_decrypt shift_rows_out ;;

    (* Different rounds perform different operations on the state before adding
       the round key; select the appropriate wire based on add_round_key_in_sel *)
    let add_round_key_in :=
        mux4 (mkpair (mkpair (mkpair mix_columns_out data) shift_rows_out) mix_columns_out)
             add_round_key_in_sel in

    (* Intermediate decryption rounds need to mix the key columns *)
    mixed_round_key <- inv_mix_columns_key round_key ;;

    key_to_add <- muxPair round_key_sel (round_key, mixed_round_key) ;;
    out <- add_round_key key_to_add add_round_key_in ;;

    (* Key expansion *)
    '(round_key, rcon) <- key_expand is_decrypt round_i (round_key, rcon) ;;

    ret (mkpair (mkpair round_key rcon) out).

  Definition cipher_step
             (is_decrypt : signal Bit) (* called op_i in OpenTitan *)
             (is_first_round : signal Bit)
             (num_rounds_regular : signal round_index)
             (key_rcon_data : signal cipher_state)
             (round_i : signal round_index)
    : cava (signal cipher_state) :=
    let '(key_rcon, data) := unpair key_rcon_data in
    let '(round_key, rcon) := unpair key_rcon in
    is_final_round <- round_i ==? num_rounds_regular;;
    (* add_round_key_in_sel :
       1 if round_i = 0, 2 if round_i = num_rounds_regular, 0 otherwise *)
    let add_round_key_in_sel := unpeel [is_first_round; is_final_round]%vector in
    is_middle_round <- nor2 (is_first_round, is_final_round) ;;
    (* round_key_sel : 1 for a decryption middle round, 0 otherwise *)
    round_key_sel <- and2 (is_middle_round, is_decrypt) ;;
    key_expand_and_round is_decrypt key_rcon_data
                         add_round_key_in_sel round_key_sel round_i.

  Definition cipher_loop
    : signal cipher_signals -> cava (signal cipher_state) :=
    loopDelayS
      (fun input_and_state : signal cipher_signals
                           * signal cipher_state =>
         let '(input, feedback_state) := input_and_state in
         (* extract signals from the input tuple *)
         let '(input, idx) := unpair input in
         let '(input, initial_state) := unpair input in
         let '(input, round_0) := unpair input in
         let '(is_decrypt, num_rounds_regular) := unpair input in

         is_first_round <- idx ==? round_0 ;;
         cipher_state <- muxPair is_first_round (feedback_state, initial_state) ;;
         cipher_step is_decrypt is_first_round num_rounds_regular
                     cipher_state idx).

  Definition cipher
             (initial_rcon_selector : signal Bit -> cava (signal round_constant))
             (num_rounds_regular round_0 : signal round_index)
             (is_decrypt : signal Bit) (* called op_i in OpenTitan *)
             (initial_key : signal key) (initial_state : signal state)
             (round_i : signal round_index)
    : cava (signal state) :=
    initial_rcon <- initial_rcon_selector is_decrypt ;;
    (* combine all the input signals *)
    let initial_cipher_state : signal cipher_state :=
        mkpair (mkpair initial_key initial_rcon) initial_state in
    let loop_input : signal cipher_signals :=
        mkpair (mkpair (mkpair (mkpair is_decrypt num_rounds_regular)
                               round_0) initial_cipher_state) round_i in
    (* run the AES loop *)
    loop_out <- cipher_loop loop_input ;;
    (* select the AES state vector as output *)
    ret (snd (unpair loop_out)).

  Context (num_rounds_regular round_0 round_1 round_final: signal (round_index)).
  Context (inc_round: signal round_index -> cava (signal round_index)).

  (* Comparable to OpenTitan aes_cipher_core but with simplified signalling *)
  Definition aes_cipher_core_simplified
    (initial_rcon_selector : signal Bit -> cava (signal round_constant))
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
      (fun '((inputs, st) : signal cipher_control_signals  * signal cipher_control_state) =>

        (* unpack inputs and state from Cava 'Pair's *)
        let '(is_decrypt, in_valid_i, out_ready_i, initial_key, initial_state)
          := unpacked_signal inputs in
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
        st <- cipher initial_rcon_selector round_final round_0 is_decrypt
                    initial_key initial_state round ;;
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
