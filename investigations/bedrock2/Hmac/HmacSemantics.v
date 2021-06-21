Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.micromega.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.Hmac.Constants.

(* Note: AesSemantics.v seems to completely ignore its control register,
   which results in a wrong specification in the sense that the specification
   might say that a transition is possible even though it isn't.
   In HmacSemantics.v, we don't attempt to model all features of the Hmac module either,
   but we do try to reveal a correct subset of the full functionality of the
   Hmac module. We only say that a transition is possible if the module has
   been configured to use the mode that we're modeling, and disallow transitions
   from an idle state that's not configured to use the mode that we're modeling. *)

Axiom sha256: list byte -> list byte.

Class timing := {
  (* Max number of consecutive polls for "done" that can return "not done",
     needed to prove termination of bedrock2 code. *)
  max_negative_done_polls: Z;
}.

Section WithParams.
  Context {word: word 32} {mem: map.map word byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}
          {tim: timing}.

  Record config_data := {
    interrupts_enabled: word; (* bit #i says if interrupt #i is enabled, i=0,1,2 *)
    pending_interrupts: word;
    hmac_en: bool;
    sha_en: bool;
    swap_endian: bool;
    swap_digest: bool;
  }.

  Definition the_only_supported_config: config_data := {|
    interrupts_enabled := word.of_Z 0;
    pending_interrupts := word.of_Z 0;
    swap_digest := false;
    swap_endian := true;
    sha_en := true;
    hmac_en := false;
  |}.

  Inductive state :=
  | IDLE(config: config_data)
  | CONSUMING(sha_buffer: list byte)
  | PROCESSING(sha_buffer: list byte)(max_cycles_until_done: Z)
  | DONE(digest_buffer: list byte).

  Inductive read_step: state -> word -> word -> state -> Prop :=
  | read_done_bit_not_done: forall b v n,
      0 < n ->
      Z.testbit (word.unsigned v) HMAC_INTR_STATE_HMAC_DONE_BIT = false ->
      read_step (PROCESSING b n)
                (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET)) v
                (PROCESSING b (n-1))
  | read_done_bit_done: forall b v n,
      Z.testbit (word.unsigned v) HMAC_INTR_STATE_HMAC_DONE_BIT = true ->
      read_step (PROCESSING b n)
                (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET)) v
                (DONE (sha256 b)).

  Inductive write_step: state -> word -> word -> state -> Prop :=
  | write_cfg: forall v s,
      0 <= word.unsigned v < 2 ^ 4 ->
      write_step (IDLE s) (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET)) v
                 (IDLE {| interrupts_enabled := interrupts_enabled s;
                          pending_interrupts := pending_interrupts s;
                          hmac_en := Z.testbit 0 (word.unsigned v);
                          sha_en := Z.testbit 1 (word.unsigned v);
                          swap_endian := Z.testbit 2 (word.unsigned v);
                          swap_digest := Z.testbit 3 (word.unsigned v); |})
  | write_intr_enable: forall v s,
      0 <= word.unsigned v < 2 ^ 3 ->
      write_step (IDLE s) (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_ENABLE_REG_OFFSET)) v
                 (IDLE {| interrupts_enabled := v;
                          pending_interrupts := pending_interrupts s;
                          hmac_en := hmac_en s;
                          sha_en := sha_en s;
                          swap_endian := swap_endian s;
                          swap_digest := swap_digest s; |})
  | write_intr_state: forall v s,
      0 <= word.unsigned v < 2 ^ 3 ->
      write_step (IDLE s) (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET)) v
                 (IDLE {| interrupts_enabled := interrupts_enabled s;
                          pending_interrupts := v; (* TODO FIX these bits are rw1c! *)
                          hmac_en := hmac_en s;
                          sha_en := sha_en s;
                          swap_endian := swap_endian s;
                          swap_digest := swap_digest s; |})
  | write_hash_start:
      write_step (IDLE the_only_supported_config)
                 (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET))
                 (word.of_Z (Z.shiftl 1 HMAC_CMD_HASH_START_BIT))
                 (CONSUMING [])
  | write_byte: forall b v,
      write_step (CONSUMING b)
                 (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET)) v
                 (CONSUMING (b ++ [byte.of_Z (word.unsigned v)]))
  | write_word: forall b v,
      write_step (CONSUMING b)
                 (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET)) v
                 (CONSUMING (b ++ le_split 4 (word.unsigned v)))
  | write_hash_process: forall b,
      write_step (CONSUMING b)
                 (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET))
                 (word.of_Z (Z.shiftl 1 HMAC_CMD_HASH_PROCESS_BIT))
                 (PROCESSING b max_negative_done_polls).

  (* TODO: Can we make these register conventions more explicit in our spec?
     ro     read-only
     wo     write-only
     rw     read/write
     rw1c   read/write, writing 1 clears the bit, writing 0 has no effect
     rw0c   read/write, writing 0 clears the bit, writing 1 has no effect
     rw1s   read/write, writing 1 sets the bit, writing 0 has no effect *)


  Definition HMAC_MMIO_START: Z :=
    TOP_EARLGREY_HMAC_BASE_ADDR.
  Definition HMAC_MMIO_PAST_END: Z :=
    TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET + HMAC_MSG_FIFO_SIZE_BYTES.

  Global Instance state_machine_parameters: StateMachineSemantics.parameters 32 word mem := {|
    StateMachineSemantics.parameters.state := state ;
    StateMachineSemantics.parameters.register := word;
    StateMachineSemantics.parameters.is_initial_state s :=
      match s with
      | IDLE _ => True
      | _ => False
      end;
    StateMachineSemantics.parameters.read_step := read_step;
    StateMachineSemantics.parameters.write_step := write_step;
    StateMachineSemantics.parameters.reg_addr := id;
    StateMachineSemantics.parameters.is_reg_addr a :=
      HMAC_MMIO_START <= word.unsigned a < HMAC_MMIO_PAST_END /\ word.unsigned a mod 4 = 0;
  |}.

  Axiom TODO: False.

  Global Instance state_machine_parameters_ok
    : StateMachineSemantics.parameters.ok state_machine_parameters.
  Proof.
    constructor.
    { left; exact eq_refl. }
    { exact word_ok. }
    { exact mem_ok. }
    { cbn. unfold id. auto. }
    { cbn. intuition auto. }
    { cbn. lia. }
    { cbn. unfold id. intros. inversion H; try lia; case TODO. }
    { cbn. unfold id. intros. inversion H; try lia; case TODO. }
  Qed.

End WithParams.
