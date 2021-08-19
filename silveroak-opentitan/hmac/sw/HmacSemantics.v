Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.micromega.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndianList.
Require Import bedrock2.ZnWords.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import HmacSoftware.Constants.

(* In HmacSemantics.v, we don't attempt to model all features of the Hmac module,
   but we do try to reveal a correct subset of the full functionality of the
   Hmac module. We only say that a transition is possible if the module has
   been configured to use the mode that we're modeling, and disallow transitions
   from an idle state that's not configured to use the mode that we're modeling. *)

Class timing := {
  (* Max number of consecutive polls for "done" that can return "not done",
     needed to prove termination of bedrock2 code. *)
  max_negative_done_polls: Z;
}.

Section WithParams.
  Context {word: word 32} {mem: map.map word byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}
          {tim: timing}.

  (* Note: sha256 only accepts messages of size up to `2^64-1` bits, so if we don't model
     this restriction, we will have to be careful to not make contradictory assumptions
     (eg if we add the MSG_LENGTH_LOWER and MSG_LENGTH_UPPER registers, we'll have to make
     sure we don't assume that any list length can fit into these 2^64 bits, because
     that would allow us to prove False). *)
  Axiom sha256: list byte -> list byte. (* returns a list of 32 bytes (=256 bits) *)

  Record idle_data := {
    (* only the lowest 3 bits count, and we only model the case where all interrupts are
       disabled, but we do have to check that the software disabled them *)
    intr_enable: word;

    (* The hmac_done rw1c bit of hmac.INTR_STATE.
       Writing true to it if true clears it (sets it to false) *)
    hmac_done: bool;

    (* The bits of hmac.CFG *)
    hmac_en: bool;
    sha_en: bool;
    swap_endian: bool; (* *false* means input is big-endian *)
    swap_digest: bool; (* *true*  means output is big-endian *)
  }.

  Inductive state :=
  | IDLE(digest_buffer: list byte)(s: idle_data)
  (* since the configuration bits of idle_data can't be modified while CONSUMING or
     PROCESSING, we don't need to include this data in these states *)
  | CONSUMING(sha_buffer: list byte)
  | PROCESSING(sha_buffer: list byte)(max_cycles_until_done: Z).

  Inductive read_step: nat -> state -> word -> word -> state -> Prop :=
  | read_done_bit_not_done: forall b v n,
      0 < n ->
      Z.testbit (word.unsigned v) HMAC_INTR_STATE_HMAC_DONE_BIT = false ->
      read_step 4 (PROCESSING b n)
                (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET)) v
                (PROCESSING b (n-1))
  | read_done_bit_done: forall b v n,
      Z.testbit (word.unsigned v) HMAC_INTR_STATE_HMAC_DONE_BIT = true ->
      read_step 4 (PROCESSING b n)
                (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET)) v
                (IDLE (sha256 b)
                      {| (* flag in INTR_STATE is set (even though interrupts are disabled) *)
                        hmac_done := true;
                        (* the remaining flags are the same as when we started processing: *)
                        intr_enable := word.of_Z 0;
                        hmac_en := false;
                        sha_en := true;
                        swap_endian := true;
                        swap_digest := false;
                      |})
  (* TODO the digest could also be read byte by byte *)
  | read_digest: forall s d i addr v,
      swap_endian s = true ->
      swap_digest s = false ->
      0 <= i < 8 ->
      addr = word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_DIGEST_7_REG_OFFSET - (i * 4)) ->
      v = word.of_Z (le_combine (List.firstn 4 (List.skipn (Z.to_nat i * 4) d))) ->
      read_step 4 (IDLE d s) addr v (IDLE d s).

  Inductive write_step: nat -> state -> word -> word -> state -> Prop :=
  | write_cfg: forall v d s,
      write_step 4 (IDLE d s) (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET)) v
                 (IDLE d {| intr_enable := intr_enable s;
                            hmac_done := hmac_done s;
                            hmac_en := Z.testbit 0 (word.unsigned v);
                            sha_en := Z.testbit 1 (word.unsigned v);
                            swap_endian := Z.testbit 2 (word.unsigned v);
                            swap_digest := Z.testbit 3 (word.unsigned v); |})
  | write_intr_enable: forall v d s,
      write_step 4 (IDLE d s) (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_ENABLE_REG_OFFSET)) v
                 (IDLE d {| intr_enable := word.and v (word.of_Z 7);
                            hmac_done := hmac_done s;
                            hmac_en := hmac_en s;
                            sha_en := sha_en s;
                            swap_endian := swap_endian s;
                            swap_digest := swap_digest s; |})
  | write_intr_state: forall v d s,
      write_step 4 (IDLE d s) (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET)) v
                 (IDLE d {| (* hmac_done is rw1c (clear on write-1) *)
                            hmac_done := if Z.testbit (word.unsigned v) HMAC_INTR_STATE_HMAC_DONE_BIT
                                         then false else hmac_done s;
                            intr_enable := intr_enable s;
                            hmac_en := hmac_en s;
                            sha_en := sha_en s;
                            swap_endian := swap_endian s;
                            swap_digest := swap_digest s; |})
  | write_hash_start: forall d v,
      v = word.of_Z (Z.shiftl 1 HMAC_CMD_HASH_START_BIT) ->
      write_step 4 (IDLE d (* Here one can see that we only model a subset of the features of
                            the HMAC module: in our model, starting the computation is only
                            possible from the specific configuration below.
                            But using an HMAC module with more features than what we expose
                            to the software is safe, so modeling only a subset is not a problem. *)
                         {| hmac_done := false;
                            intr_enable := word.of_Z 0;
                            hmac_en := false;
                            sha_en := true;
                            swap_endian := true;
                            swap_digest := false; |})
                 (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET)) v
                 (CONSUMING [])
  | write_byte: forall bs bs' v,
      0 <= word.unsigned v < 2 ^ 8 ->
      bs' = bs ++ [byte.of_Z (word.unsigned v)] ->
      write_step 1 (CONSUMING bs)
                 (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET)) v
                 (CONSUMING bs')
  | write_word: forall bs bs' v,
      bs' = bs ++ le_split 4 (word.unsigned v) ->
      write_step 4 (CONSUMING bs)
                 (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET)) v
                 (CONSUMING bs')
  | write_hash_process: forall b v,
      v = word.of_Z (Z.shiftl 1 HMAC_CMD_HASH_PROCESS_BIT) ->
      write_step 4 (CONSUMING b)
                 (word.of_Z (TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET)) v
                 (PROCESSING b max_negative_done_polls).

  (* TODO: Can we make these register conventions more explicit in our spec?
     https://docs.opentitan.org/doc/rm/register_tool/
     none       No access
     ro         Read Only
     rc         Read Only, reading clears
     rw         Read/Write
     r0w1c      Read zero, Write with 1 clears
     rw1s       Read, Write with 1 sets
     rw1c       Read, Write with 1 clears
     rw0c       Read, Write with 0 clears
     wo         Write Only
   *)

  Definition HMAC_MMIO_START: Z :=
    TOP_EARLGREY_HMAC_BASE_ADDR.
  Definition HMAC_MMIO_PAST_END: Z :=
    TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET + HMAC_MSG_FIFO_SIZE_BYTES.

  Global Instance hmac_state_machine : state_machine.parameters := {|
    state_machine.state := state ;
    state_machine.register := word;
    state_machine.is_initial_state s :=
      match s with
      | IDLE digest_buffer _ => List.length digest_buffer = 8%nat
      | _ => False
      end;
    state_machine.read_step := read_step;
    state_machine.write_step := write_step;
    state_machine.reg_addr := id;
    state_machine.isMMIOAddr a := HMAC_MMIO_START <= word.unsigned a < HMAC_MMIO_PAST_END;
  |}.

  Global Instance hmac_state_machine_ok : state_machine.ok hmac_state_machine.
  Proof.
    constructor; cbn; unfold id; intros; try exact _;
      match goal with
      | H: read_step _ _ _ _ _ |- _ => inversion H
      | H: write_step _ _ _ _ _ |- _ => inversion H
      | |- _ => idtac
      end;
      subst;
      try ZnWords.
  Qed.

End WithParams.
