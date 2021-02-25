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

From RecordUpdate Require Import RecordSet.

Require Import Cava.Cava.
Require Import Cava.Acorn.Circuit.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.Combinators.
Require Import AcornAes.Pkg.
Require Import AcornAes.SubBytesCircuit.
Require Import AcornAes.AddRoundKeyCircuit.
Require Import AcornAes.ShiftRowsCircuit.
Require Import AcornAes.MixColumnsCircuit.
Require Import AcornAes.CipherCircuit.
Import Circuit.Notations.
Existing Instance CavaCombinationalNet.

Require Import AcornAes.ShiftRowsNetlist.
Require Import AcornAes.MixColumnsNetlist.
Require Import AcornAes.SubBytesNetlist.

Local Open Scope monad_scope.
Local Open Scope vector_scope.

Notation round_index := (Vec Bit 4) (only parsing).

Section WithCava.
  Context {signal} {semantics : Cava signal}.

  Local Infix "==?" := eqb (at level 40).

  Section PkgNotations.
    Import Pkg.Notations.

    Context (key_expand :
               Circuit (signal Bit * signal round_index * signal round_index
                        * signal round_index * signal key * signal state)
                       (signal key)).

    Definition round_0: signal round_index :=
      unpeel (Vector.map constant (nat_to_bitvec_sized _ 0)).
    Definition round_final: signal round_index :=
      unpeel (Vector.map constant (nat_to_bitvec_sized _ 13)).
    Definition round_14: signal round_index :=
      unpeel (Vector.map constant (nat_to_bitvec_sized _ 14)).

    Definition round_1: signal round_index :=
      unpeel (Vector.map constant (nat_to_bitvec_sized _ 1)).

    Definition inc_round (current: signal round_index): cava (signal round_index) :=
      let sum := (@unsignedAdd _ _ 4 4 (current, round_1)) in
      let '(trunc,_) := unsnoc (peel sum) in
      localSignal (unpeel trunc).

    (* aes_shift_rows' and aes_mix_columns' must be instantiated hierarchically
       to prevent excessive code generation
       *)
    Definition aes_shift_rows' x y :=
      instantiate aes_shift_rows_Interface (fun '(x,y) => aes_shift_rows x y) (x, y).
    Definition aes_mix_columns' x y :=
      instantiate aes_mix_columns_Interface (fun '(x,y) => aes_shift_rows x y) (x, y).
    Definition aes_sbox_lut' x y :=
      instantiate aes_sbox_lut_Interface (fun '(x,y) => aes_sbox_lut x y) (x, y).
    Definition aes_sub_bytes' (is_decrypt : signal Bit) (b : signal state)
      : cava (signal state) := state_map (aes_sbox_lut' is_decrypt) b.

    Definition inv_mix_columns_key := aes_mix_columns' (constant true).

    (* Plug in our concrete components to the skeleton in Cipher.v *)
    Definition cipher := CipherCircuit.cipher
      aes_sub_bytes' aes_shift_rows' aes_mix_columns' aes_add_round_key
      inv_mix_columns_key key_expand.
  End PkgNotations.

  Record cipher_control_signals {f: SignalType -> Type} :=
    { in_ready_o : f Bit
    ; out_valid_o : f Bit
    (* ; crypt_o : f Bit *)
    (* ; dec_key_gen_o : f Bit *)
    (* ; key_clear_o : f Bit *)
    (* ; data_out_clear_o : f Bit *)
    ; state_we_o : f Bit
    ; key_full_we_o : f Bit
    ; key_dec_we_o : f Bit
    ; key_expand_step_o : f Bit
    ; key_expand_clear_o : f Bit
    (* ; key_expand_round_o : f (Vec Bit 4) *)
    ; state_sel_o : f (Vec Bit 2)
    ; add_rk_sel_o : f (Vec Bit 2)
    (* ; key_expand_op_o : f (Vec Bit 2) *)
    ; key_full_sel_o: f (Vec Bit 2)
    ; key_dec_sel_o : f Bit
    ; key_words_sel_o : f (Vec Bit 2)
    ; round_key_sel_o : f Bit

    ; aes_cipher_ctrl_ns : f (Vec Bit 3)

    ; round_d : f (Vec Bit 4)
    ; num_rounds_d : f (Vec Bit 4)
    ; num_rounds_regular : f (Vec Bit 4)

    ; crypt_d : f Bit
    ; dec_key_gen_d : f Bit
    ; key_clear_d : f Bit
    ; data_out_clear_d : f Bit
    }.
  Arguments cipher_control_signals : clear implicits.

  Definition bitvec_to_signal {n : nat} (lut : t bool n) : signal (Vec Bit n) :=
    unpeel (Vector.map constant lut).

  Definition IDLE_S := bitvec_to_signal (nat_to_bitvec_sized 3 0).
  Definition INIT_S := bitvec_to_signal (nat_to_bitvec_sized 3 1).
  Definition ROUND_S := bitvec_to_signal (nat_to_bitvec_sized 3 2).
  Definition FINISH_S := bitvec_to_signal (nat_to_bitvec_sized 3 3).
  Definition CLEAR_S_S := bitvec_to_signal (nat_to_bitvec_sized 3 4).
  Definition CLEAR_KD_S := bitvec_to_signal (nat_to_bitvec_sized 3 5).

  Definition STATE_INIT := bitvec_to_signal (nat_to_bitvec_sized 2 0).
  Definition STATE_ROUND := bitvec_to_signal (nat_to_bitvec_sized 2 1).
  Definition STATE_CLEAR := bitvec_to_signal (nat_to_bitvec_sized 2 2).

  Definition KEY_FULL_ENC_INIT := bitvec_to_signal (nat_to_bitvec_sized 2 0).
  Definition KEY_FULL_DEC_INIT := bitvec_to_signal (nat_to_bitvec_sized 2 1).
  Definition KEY_FULL_ROUND := bitvec_to_signal (nat_to_bitvec_sized 2 2).
  Definition KEY_FULL_CLEAR := bitvec_to_signal (nat_to_bitvec_sized 2 3).

  Definition ADD_RK_INIT := bitvec_to_signal (nat_to_bitvec_sized 2 0).
  Definition ADD_RK_ROUND := bitvec_to_signal (nat_to_bitvec_sized 2 1).
  Definition ADD_RK_FINAL := bitvec_to_signal (nat_to_bitvec_sized 2 2).

  Definition KEY_INIT_INPUT := constant false.
  Definition KEY_INIT_CLEAR := constant true.

  Definition KEY_DEC_EXPAND := constant false.
  Definition KEY_DEC_CLEAR := constant true.

  Definition KEY_WORDS_0123 := bitvec_to_signal (nat_to_bitvec_sized 2 0).
  Definition KEY_WORDS_2345 := bitvec_to_signal (nat_to_bitvec_sized 2 1).
  Definition KEY_WORDS_4567 := bitvec_to_signal (nat_to_bitvec_sized 2 3).
  Definition KEY_WORDS_ZERO := bitvec_to_signal (nat_to_bitvec_sized 2 4).

  Definition AES_128 := bitvec_to_signal (nat_to_bitvec_sized 3 1).
  Definition AES_192 := bitvec_to_signal (nat_to_bitvec_sized 3 2).
  Definition AES_256 := bitvec_to_signal (nat_to_bitvec_sized 3 4).

  Definition ROUND_KEY_DIRECT := constant false.
  Definition ROUND_KEY_MIXED := constant true.

  Definition cava_signal := (fun x => cava (signal x)).

  Instance settableSignals : Settable _ := settable! (Build_cipher_control_signals cava_signal)
    < in_ready_o; out_valid_o;
    state_we_o; key_full_we_o; key_dec_we_o; key_expand_step_o; key_expand_clear_o;
    state_sel_o; add_rk_sel_o; key_full_sel_o;
    key_dec_sel_o; key_words_sel_o; round_key_sel_o; aes_cipher_ctrl_ns; round_d;
    num_rounds_d; num_rounds_regular; crypt_d; dec_key_gen_d; key_clear_d;
    data_out_clear_d >.

  Record cipher_control_inputs :=
    { in_valid_i : signal Bit
    ; out_ready_i : signal Bit
    ; crypt_i : signal Bit
    ; dec_key_gen_i : signal Bit
    ; key_clear_i : signal Bit
    ; data_out_clear_i : signal Bit
    ; op_i : signal Bit
    ; key_len_i : signal (Vec Bit 3)
    }.

  Definition natural_transform {F G}
    (x: cipher_control_signals F)
    (ret: forall {x}, F x -> G x) : cipher_control_signals G :=
    match x with
    | Build_cipher_control_signals _ a b c d e f g h i j k l m n o p q r s t u =>
      Build_cipher_control_signals _
      (ret a) (ret b) (ret c) (ret d) (ret e) (ret f) (ret g)
      (ret h) (ret i) (ret j) (ret k) (ret l) (ret m) (ret n)
      (ret o) (ret p) (ret q) (ret r) (ret s) (ret t) (ret u)
    end.

  Definition convolution {F G H}
    (x: cipher_control_signals F)
    (y: cipher_control_signals G)
    (ap: forall {x}, F x -> G x -> H x) : cipher_control_signals H :=
    match x, y with
    | Build_cipher_control_signals _
      a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 m1 n1 o1 p1 q1 r1 s1 t1 u1,
      Build_cipher_control_signals _
      a2 b2 c2 d2 e2 f2 g2 h2 i2 j2 k2 l2 m2 n2 o2 p2 q2 r2 s2 t2 u2 =>
      Build_cipher_control_signals _
      (ap a1 a2) (ap b1 b2) (ap c1 c2) (ap d1 d2) (ap e1 e2) (ap f1 f2) (ap g1 g2)
      (ap h1 h2) (ap i1 i2) (ap j1 j2) (ap k1 k2) (ap l1 l2) (ap m1 m2) (ap n1 n2)
      (ap o1 o2) (ap p1 p2) (ap q1 q2) (ap r1 r2) (ap s1 s2) (ap t1 t2) (ap u1 u2)
    end.

  Definition lift_to_circuit (x: cipher_control_signals signal): cipher_control_signals cava_signal
    := natural_transform x (fun _ x => ret x).

  Definition vector_cava_signal n := (fun x => cava (Vector.t (signal x) n)).

  Definition extend_nondeterministic_state  {n}
    (x: cipher_control_signals cava_signal)
    (xs: cipher_control_signals (vector_cava_signal n))
    : cipher_control_signals (vector_cava_signal (S n)) :=
    convolution x xs (
      fun _ x xs =>
      s <- x ;;
      v <- xs ;;
      ret (s :: v)).

  Fixpoint nondeterministic_state {n}
    (xs: Vector.t (cipher_control_signals cava_signal) n)
    : cipher_control_signals (vector_cava_signal n) :=
    match xs with
    | [] => Build_cipher_control_signals _
      (ret []) (ret []) (ret []) (ret []) (ret []) (ret []) (ret [])
      (ret []) (ret []) (ret []) (ret []) (ret []) (ret []) (ret [])
      (ret []) (ret []) (ret []) (ret []) (ret []) (ret []) (ret [])
    | x :: xs' => extend_nondeterministic_state x (nondeterministic_state xs')
    end.

  Definition select_state {n sel_sz}
    (x: cipher_control_signals (vector_cava_signal n))
    (sel: cava (signal (Vec Bit sel_sz)))
    : cipher_control_signals cava_signal :=
    natural_transform x (fun _ xs =>
      v <- xs ;;
      v' <- localSignal (unpeel v) ;;
      sel' <- sel ;;
      localSignal (indexAt v' sel')
    ).

  Definition signal_update := state (cipher_control_signals cava_signal) unit.
  Definition setSignal {T} F {_: Setter F} (x: cava_signal T) : signal_update :=
    s <- get ;;
    let s' := set F (fun _ => x) s in
    put s.
  Definition setSignal1 {T} F {_: Setter F} (x: signal T) : signal_update :=
    setSignal F (ret x).
  Definition getSignal {T} (f: cipher_control_signals cava_signal -> T)
    : state (cipher_control_signals cava_signal) T :=
    s <- get ;;
    ret (f s).
  Definition updateSignal {T} F {_: Setter F} (f: signal T -> cava_signal T) : signal_update :=
    s <- get ;;
    let s' := set F (fun x => x >>= f) s in
    put s.
  Definition setEnSignal {T} F {_: Setter F} (en: cava_signal Bit) (x: cava_signal T)
    : signal_update :=
    s <- get ;;
    let s' := set F (fun y =>
      en' <- en ;;
      x' <- x ;;
      y' <- y ;;
      muxPair en' (y',x')) s in
    put s.
  Definition setEnSignal1 {T} F {_: Setter F} (en: cava_signal Bit) (x: signal T) : signal_update :=
    setEnSignal F en (ret x).

  Definition andCond (x y: cava_signal Bit): cava_signal Bit :=
    x' <- x;;
    y' <- y;;
    and2 (x', y').

  Definition transition_idle_pre: signal_update :=
    setSignal1 dec_key_gen_d (constant false) ;;
    setSignal1 in_ready_o (constant true).

  Definition transition_idle_clear (inputs: cipher_control_inputs): signal_update :=
    transition_idle_pre ;;
    (* // Clear internal key registers. The cipher core muxes are used to clear the data *)
    (* // output registers. *)
    (* key_clear_d      = key_clear_i; *)
    (* data_out_clear_d = data_out_clear_i; *)

    (* // To clear the data output registers, we must first clear the state. *)
    (* aes_cipher_ctrl_ns = data_out_clear_i ? CLEAR_S : CLEAR_KD; *)
    setSignal1 key_clear_d (key_clear_i inputs) ;;
    setSignal1 data_out_clear_d (data_out_clear_i inputs) ;;
    setSignal aes_cipher_ctrl_ns (muxPair (data_out_clear_i inputs) (CLEAR_KD_S, CLEAR_S_S)).

  Definition transition_idle_start (inputs: cipher_control_inputs): signal_update :=
    transition_idle_pre ;;

    let dec_key_gen_i' := dec_key_gen_i inputs in
    let op_i' := op_i inputs in

    (* // Start encryption/decryption or generation of start key for decryption. *)
    (* crypt_d       = ~dec_key_gen_i; *)
    (* dec_key_gen_d =  dec_key_gen_i; *)
    setSignal crypt_d (inv dec_key_gen_i') ;;
    setSignal1 dec_key_gen_d dec_key_gen_i' ;;

    (* // Load input data to state *)
    (* state_sel_o = dec_key_gen_d ? STATE_CLEAR : STATE_INIT; *)
    (* state_we_o  = 1'b1; *)
    setSignal state_sel_o (muxPair dec_key_gen_i' (STATE_INIT, STATE_CLEAR)) ;;
    setSignal1 state_we_o (constant true) ;;

    (* // Init key expand *)
    (* key_expand_clear_o = 1'b1; *)
    setSignal1 key_expand_clear_o (constant true) ;;

    (* // Load full key *)
    (* key_full_sel_o = dec_key_gen_d ? KEY_FULL_ENC_INIT : *)
    (*             (op_i == CIPH_FWD) ? KEY_FULL_ENC_INIT : *)
    (*                                  KEY_FULL_DEC_INIT; *)
    setSignal key_full_sel_o (
      temp <- muxPair op_i' (KEY_FULL_ENC_INIT, KEY_FULL_DEC_INIT) ;;
      muxPair dec_key_gen_i' (temp, KEY_FULL_ENC_INIT)) ;;
    (* key_full_we_o  = 1'b1; *)
    setSignal1 key_full_we_o (constant true) ;;

    (* // Load num_rounds, clear round *)
    (* round_d      = '0; *)
    setSignal1 round_d round_0 ;;
    (* num_rounds_d = (key_len_i == AES_128) ? 4'd10 : *)
    (*                (key_len_i == AES_192) ? 4'd12 : *)
    (*                                         4'd14; *)
    setSignal1 num_rounds_d round_14 ;;
    (* aes_cipher_ctrl_ns = INIT; *)
    setSignal1 aes_cipher_ctrl_ns INIT_S.

  (* mux idle states *)
  Definition transition_idle (inputs: cipher_control_inputs): signal_update :=
    s <- get ;;
    let clear_transition := execState (transition_idle_clear inputs) s in
    let start_transition := execState (transition_idle_start inputs) s in
    let state_matrix :=
      nondeterministic_state [s; clear_transition; start_transition] in
    (* if (in_valid_i) begin *)
    let cond1 := ret (in_valid_i inputs) in
    (* if (key_clear_i || data_out_clear_i) begin *)
    let cond2 := andCond cond1 (or2 (key_clear_i inputs, data_out_clear_i inputs)) in
    (* end else if (dec_key_gen_i || crypt_i) begin *)
    let cond3 := andCond cond1 (or2 (dec_key_gen_i inputs, crypt_i inputs)) in
    let sel0 := bitvec_to_signal (nat_to_bitvec_sized 2 0) in
    let sel1 := bitvec_to_signal (nat_to_bitvec_sized 2 1) in
    let sel2 := bitvec_to_signal (nat_to_bitvec_sized 2 2) in
    let sel :=
      cond3' <- cond3 ;;
      x <- muxPair cond3' (sel0, sel2) ;;
      cond2' <- cond2 ;;
      muxPair cond2' (x, sel1) in
    put (select_state state_matrix sel).


  Definition transition_init (inputs: cipher_control_inputs): signal_update :=
    dec_key_gen_q <- getSignal dec_key_gen_d ;;
    (* // Initial round: just add key to state *)
    (* state_we_o   = ~dec_key_gen_q; *)
    (* add_rk_sel_o = ADD_RK_INIT; *)
    setSignal state_we_o (dec_key_gen_q >>= inv) ;;
    setSignal1 add_rk_sel_o ADD_RK_INIT;;

    (* // Select key words for initial add_round_key *)
    (* key_words_sel_o = dec_key_gen_q                ? KEY_WORDS_ZERO : *)
    (*     (key_len_i == AES_128)                     ? KEY_WORDS_0123 : *)
    (*     (key_len_i == AES_192 && op_i == CIPH_FWD) ? KEY_WORDS_0123 : *)
    (*     (key_len_i == AES_192 && op_i == CIPH_INV) ? KEY_WORDS_2345 : *)
    (*     (key_len_i == AES_256 && op_i == CIPH_FWD) ? KEY_WORDS_0123 : *)
    (*     (key_len_i == AES_256 && op_i == CIPH_INV) ? KEY_WORDS_4567 : KEY_WORDS_ZERO; *)
    setSignal key_words_sel_o (
      (* TODO(blaxill): support other key sizes *)
      dec_key_gen_q' <- dec_key_gen_q ;;
      sel <- muxPair (op_i inputs) (KEY_WORDS_4567, KEY_WORDS_0123) ;;
      muxPair dec_key_gen_q' (sel, KEY_WORDS_ZERO)
      ) ;;

    (* // Make key expand advance - AES-256 has two round keys available right from beginning. *)
    (* if (key_len_i != AES_256) begin *)
    (*   key_expand_step_o = 1'b1; *)
    (*   key_full_we_o     = 1'b1; *)
    (* end *)
    let cond := eqb (key_len_i inputs) AES_256 >>= inv in
    setEnSignal1 key_expand_step_o cond (constant true) ;;
    setEnSignal1 key_full_we_o cond (constant true) ;;

    (* aes_cipher_ctrl_ns = ROUND; *)
    setSignal1 aes_cipher_ctrl_ns ROUND_S.

  Definition transition_round (inputs: cipher_control_inputs): signal_update :=
    dec_key_gen_q <- getSignal dec_key_gen_d ;;
    round_q <- getSignal round_d ;;
    num_rounds_regular' <- getSignal num_rounds_regular ;;
    (* // Normal rounds *)
    (* state_we_o = ~dec_key_gen_q; *)
    setSignal state_we_o (dec_key_gen_q >>= inv) ;;

    (* // Select key words for add_round_key *)
    (* key_words_sel_o = dec_key_gen_q                ? KEY_WORDS_ZERO : *)
    (*     (key_len_i == AES_128)                     ? KEY_WORDS_0123 : *)
    (*     (key_len_i == AES_192 && op_i == CIPH_FWD) ? KEY_WORDS_2345 : *)
    (*     (key_len_i == AES_192 && op_i == CIPH_INV) ? KEY_WORDS_0123 : *)
    (*     (key_len_i == AES_256 && op_i == CIPH_FWD) ? KEY_WORDS_4567 : *)
    (*     (key_len_i == AES_256 && op_i == CIPH_INV) ? KEY_WORDS_0123 : KEY_WORDS_ZERO; *)
    setSignal key_words_sel_o (
      (* TODO(blaxill): support other key sizes *)
      dec_key_gen_q' <- dec_key_gen_q ;;
      sel <- muxPair (op_i inputs) (KEY_WORDS_4567, KEY_WORDS_0123) ;;
      muxPair dec_key_gen_q' (sel, KEY_WORDS_ZERO)
      ) ;;

    (* // Make key expand advance *)
    (* key_expand_step_o = 1'b1; *)
    setSignal1 key_expand_step_o (constant true) ;;
    (* key_full_we_o     = 1'b1; *)
    setSignal1 key_full_we_o (constant true) ;;

    (* // Select round key: direct or mixed (equivalent inverse cipher) *)
    (* round_key_sel_o = (op_i == CIPH_FWD) ? ROUND_KEY_DIRECT : ROUND_KEY_MIXED; *)
    setSignal round_key_sel_o (muxPair (op_i inputs) (ROUND_KEY_DIRECT, ROUND_KEY_MIXED)) ;;

    (* // Update round *)
    (* round_d = round_q + 4'b1; *)
    updateSignal round_d inc_round ;;

    (* // Are we doing the last regular round? *)
    (* if (round_q == num_rounds_regular) begin *)
    let cond :=
      num_rounds_regular'' <- num_rounds_regular' ;;
      round_q' <- round_q ;;
      eqb round_q' num_rounds_regular'' in
    (*   aes_cipher_ctrl_ns = FINISH; *)
    setEnSignal1 aes_cipher_ctrl_ns cond FINISH_S ;;

    (*   if (dec_key_gen_q) begin *)
    let cond2 := andCond cond dec_key_gen_q in
    (*     // Write decryption key. *)
    (*     key_dec_we_o = 1'b1; *)
    setEnSignal1 key_dec_we_o cond2 (constant true) ;;
    (*     // Indicate that we are done, try to perform the handshake. But we don't wait here *)
    (*     // as the decryption key is valid only during one cycle. If we don't get the *)
    (*     // handshake now, we will wait in the finish state. *)
    (*     out_valid_o = 1'b1; *)
    setEnSignal1 out_valid_o cond2 (constant true) ;;
    (*     if (out_ready_i) begin *)
    let cond3 := andCond cond2 (ret (out_ready_i inputs)) in
    (*       // Go to idle state directly. *)
    (*       dec_key_gen_d      = 1'b0; *)
    setEnSignal1 out_valid_o cond3 (constant false) ;;
    (*       aes_cipher_ctrl_ns = IDLE; *)
    setEnSignal1 aes_cipher_ctrl_ns cond3 IDLE_S.

  Definition transition_finish (inputs: cipher_control_inputs): signal_update :=
    dec_key_gen_q <- getSignal dec_key_gen_d ;;
    round_q <- getSignal round_d ;;
    num_rounds_regular' <- getSignal num_rounds_regular ;;

    (* // Select key words for add_round_key *)
    (* key_words_sel_o = dec_key_gen_q                ? KEY_WORDS_ZERO : *)
    (*     (key_len_i == AES_128)                     ? KEY_WORDS_0123 : *)
    (*     (key_len_i == AES_192 && op_i == CIPH_FWD) ? KEY_WORDS_2345 : *)
    (*     (key_len_i == AES_192 && op_i == CIPH_INV) ? KEY_WORDS_0123 : *)
    (*     (key_len_i == AES_256 && op_i == CIPH_FWD) ? KEY_WORDS_4567 : *)
    (*     (key_len_i == AES_256 && op_i == CIPH_INV) ? KEY_WORDS_0123 : KEY_WORDS_ZERO; *)
    setSignal key_words_sel_o (
      (* TODO(blaxill): support other key sizes *)
      dec_key_gen_q' <- dec_key_gen_q ;;
      sel <- muxPair (op_i inputs) (KEY_WORDS_4567, KEY_WORDS_0123) ;;
      muxPair dec_key_gen_q' (sel, KEY_WORDS_ZERO)
      ) ;;

    (* // Skip mix_columns *)
    (* add_rk_sel_o = ADD_RK_FINAL; *)
    setSignal1 add_rk_sel_o ADD_RK_FINAL ;;

    (* // Indicate that we are done, wait for handshake. *)
    (* out_valid_o = 1'b1; *)
    setSignal1 out_valid_o (constant true) ;;
    (* if (out_ready_i) begin *)
    let cond := (ret (out_ready_i inputs)) in
    (*   // We don't need the state anymore, clear it. *)
    (*   state_we_o         = 1'b1; *)
    setEnSignal1 state_we_o cond (constant true) ;;
    (*   state_sel_o        = STATE_CLEAR; *)
    setEnSignal1 state_sel_o cond STATE_CLEAR ;;
    (*   crypt_d            = 1'b0; *)
    setEnSignal1 crypt_d cond (constant false) ;;
    (*   // If we were generating the decryption key and didn't get the handshake in the last *)
    (*   // regular round, we should clear dec_key_gen now. *)
    (*   dec_key_gen_d      = 1'b0; *)
    setEnSignal1 dec_key_gen_d cond (constant false) ;;
    (*   aes_cipher_ctrl_ns = IDLE; *)
    setEnSignal1 aes_cipher_ctrl_ns cond IDLE_S.

  Definition transition_clear (inputs: cipher_control_inputs): signal_update :=
    (* // Clear the state with pseudo-random data. *)
    (* state_we_o         = 1'b1; *)
    setSignal1 state_we_o (constant true) ;;
    (* state_sel_o        = STATE_CLEAR; *)
    setSignal1 state_sel_o STATE_CLEAR ;;
    (* aes_cipher_ctrl_ns = CLEAR_KD; *)
    setSignal1 aes_cipher_ctrl_ns CLEAR_KD_S.

  Definition transition_clear_kd (inputs: cipher_control_inputs): signal_update :=
    (* // Clear internal key registers and/or external data output registers. *)
    (* if (key_clear_q) begin *)
    key_clear_q <- getSignal key_clear_d ;;
    (*   key_full_sel_o = KEY_FULL_CLEAR; *)
    setEnSignal1 key_full_sel_o key_clear_q KEY_FULL_CLEAR ;;
    (*   key_full_we_o  = 1'b1; *)
    setEnSignal1 key_full_we_o key_clear_q (constant true) ;;
    (*   key_dec_sel_o  = KEY_DEC_CLEAR; *)
    setEnSignal1 key_dec_sel_o key_clear_q KEY_DEC_CLEAR ;;
    (*   key_dec_we_o   = 1'b1; *)
    setEnSignal1 key_dec_we_o key_clear_q (constant true) ;;
    (* end *)
    (* if (data_out_clear_q) begin *)
    data_out_clear_q <- getSignal data_out_clear_d ;;
    (*   // Forward the state (previously cleared with psuedo-random data). *)
    (*   add_rk_sel_o    = ADD_RK_INIT; *)
    setEnSignal1 add_rk_sel_o data_out_clear_q ADD_RK_INIT ;;
    (*   key_words_sel_o = KEY_WORDS_ZERO; *)
    setEnSignal1 key_words_sel_o data_out_clear_q KEY_WORDS_ZERO ;;
    (*   round_key_sel_o = ROUND_KEY_DIRECT; *)
    setEnSignal1 round_key_sel_o data_out_clear_q ROUND_KEY_DIRECT ;;
    (* end *)
    (* // Indicate that we are done, wait for handshake. *)
    (* out_valid_o = 1'b1; *)
    setSignal1 out_valid_o (constant true) ;;
    (* if (out_ready_i) begin *)
    let out_ready_i' := ret (out_ready_i inputs) in
    (*   key_clear_d        = 1'b0; *)
    setEnSignal1 key_clear_d out_ready_i' (constant false) ;;
    (*   data_out_clear_d   = 1'b0; *)
    setEnSignal1 data_out_clear_d out_ready_i' (constant false) ;;
    (*   aes_cipher_ctrl_ns = IDLE; *)
    setEnSignal1 aes_cipher_ctrl_ns out_ready_i' IDLE_S.

  Definition next_transition (inputs: cipher_control_inputs): signal_update :=
    current_state <- getSignal aes_cipher_ctrl_ns ;;
    st <- get ;;
    let state_matrix := nondeterministic_state (
      Vector.map (fun f => execState (f inputs) st)
        [ transition_idle
        ; transition_init
        ; transition_round
        ; transition_finish
        ; transition_clear
        ; transition_clear_kd]) in
    put (select_state state_matrix current_state).


End WithCava.

Section PkgNotations.
  Import Pkg.Notations.
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

  (* TODO: provide a key expand implementation instead of using a black box here? *)
  Definition key_expand :
    Circuit (Signal Bit * Signal round_index * Signal round_index
             * Signal round_index * Signal key * Signal state)
            (Signal key) :=
    Loop
      (Comb
         (fun '(op_i, _, round_0, round_i, init_key, _, feedback_key) =>
            is_first_round <- eqb round_i round_0 ;;
            k <- muxPair is_first_round (feedback_key, init_key) ;;
            key_o <- blackBoxNet aes_key_expand_Interface
                                (op_i, constant true, constant false, round_i,
                                 unpeel (Vector.map constant [true;false;false]), k) ;;
            ret (key_o, key_o))).
End PkgNotations.
