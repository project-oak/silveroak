Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Array.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.Loops.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ZnWords.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.Simp.
Require Import coqutil.Tactics.letexists.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.StateMachineProperties.
Require Import Bedrock2Experiments.Tactics.
Require Import Bedrock2Experiments.Word.
Require Import Bedrock2Experiments.WordProperties.
Require Import Bedrock2Experiments.Hmac.Constants.
Require Import Bedrock2Experiments.Hmac.HmacSemantics.
Require Import Bedrock2Experiments.Hmac.Hmac.
Require Import Bedrock2Experiments.LibBase.AbsMMIOProperties.
Require Import Bedrock2Experiments.LibBase.BitfieldProperties.
Require Import Bedrock2Experiments.LibBase.MMIOLabels.
Import Syntax.Coercions List.ListNotations PrimitivePair.pair HList.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(* bedrock2.ProgramLogic does cbv, which unfolds all constants *)
Ltac normalize_body_of_function f ::= Tactics.rdelta.rdelta f.

Section Proofs.
  Context {word: word.word 32} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {timing: timing}.

  (* Plug in the right state machine parameters; typeclass inference struggles here *)
  Local Notation execution := (execution (M:=hmac_state_machine)).

  Add Ring wring : (Properties.word.ring_theory (word := word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := word)),
         constants [Properties.word_cst]).

(*
  Ltac solve_status_valid :=
    eexists; ssplit; try reflexivity;
      cbv [is_flag_set]; boolsimpl;
      repeat lazymatch goal with
             | |- (_ && _)%bool = true => apply Bool.andb_true_iff; split
             | |- negb _ = true => apply Bool.negb_true_iff
             end;
      rewrite word.unsigned_eqb;
      unfold UART_STATUS_TXEMPTY_BIT;
      unfold UART_STATUS_TXIDLE_BIT;
      unfold UART_STATUS_TXFULL_BIT;
      first [ apply Z.eqb_eq | apply Z.eqb_neq ];
      push_unsigned;
      repeat rewrite Z.shiftl_1_l;
      repeat rewrite word.wrap_small;
      simpl;
      lia.

  Lemma status_read_always_ok s :
    exists val s', read_step s STATUS val s'.
  Proof.
    destruct s; unfold read_step; cbn [read_step status_matches_state].
    { exists (word.or (word.slu (word.of_Z 1) (word.of_Z UART_STATUS_TXEMPTY_BIT))
                      (word.slu (word.of_Z 1) (word.of_Z UART_STATUS_TXIDLE_BIT))).
      solve_status_valid.
    }
    { destruct (Nat.eqb txlvl 0)%bool eqn:H.
      { apply Nat.eqb_eq in H. subst.
        exists (word.slu (word.of_Z 1) (word.of_Z UART_STATUS_TXEMPTY_BIT)).
        solve_status_valid. }
      { destruct txlvl; [discriminate | ].
        destruct (Nat.ltb (S txlvl) 32)%bool eqn:Hl.
        { exists (word.of_Z 0).
          solve_status_valid. }
        { exists (word.slu (word.of_Z 1) (word.of_Z UART_STATUS_TXFULL_BIT)).
          solve_status_valid. }
      }
    }
  Qed.
*)

  Lemma execution_unique (t : trace) s1 s2 :
    execution t s1 ->
    execution t s2 ->
    s1 = s2.
  Proof.
    eapply StateMachineProperties.execution_unique; intros;
      cbn [state_machine.is_initial_state state_machine.read_step state_machine.write_step
           hmac_state_machine] in *; simp.

all: try         match goal with
               | H: read_step _ _ _ _ _ |- _ => inversion H; subst; clear H
               | H: write_step _ _ _ _ _ |- _ => inversion H; subst; clear H
               end.
4: {
Abort.

  (* TODO move to bedrock2? *)
  Notation bytearray := (array (mem := mem) ptsto (word.of_Z 1)).
  Notation wordarray := (array (mem := mem) scalar32 (word.of_Z 4)).

  Global Instance spec_of_hmac_sha256_init : spec_of b2_hmac_sha256_init :=
    fun function_env =>
      forall tr m (R : mem -> Prop) (s : state) (digest_buffer: list word) (d: idle_data),
      R m ->
      execution tr (IDLE digest_buffer d) ->
      call function_env b2_hmac_sha256_init tr m []
        (fun tr' m' rets =>
            rets = [] /\ execution tr' (CONSUMING []) /\ R m').

  Fail Lemma hmac_sha256_init_correct :
    program_logic_goal_for_function! b2_hmac_sha256_init.
  (* bitfield_bit32_write is missing
  Proof. Qed. *)

  Global Instance spec_of_hmac_sha256_update : spec_of b2_hmac_sha256_update :=
    fun function_env =>
      forall tr m (R : mem -> Prop) (s : state) (previous_input new_input: list Byte.byte) data_addr len,
      word.unsigned len = Z.of_nat (length new_input) ->
      data_addr <> word.of_Z 0 ->
      (bytearray data_addr new_input * R)%sep m ->
      execution tr (CONSUMING previous_input) ->
      call function_env b2_hmac_sha256_update tr m [data_addr; len]
        (fun tr' m' rets =>
           rets = [word.of_Z Constants.kErrorOk] /\
           execution tr' (CONSUMING (previous_input ++ new_input)) /\
           (bytearray data_addr new_input * R)%sep m').

  Lemma hmac_sha256_update_correct :
    program_logic_goal_for_function! b2_hmac_sha256_update.
  Proof.
    repeat straightline.
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    repeat straightline.
    subst v.
    rewrite word.unsigned_if.
    rewrite word.eqb_ne by assumption.
    rewrite word.unsigned_of_Z_0.
    split; intros E. 1: exfalso; apply E; reflexivity.
    clear E.
    repeat straightline.
    eapply (while ["fifo_reg"; "data_sent"; "data"; "len"]
                  (fun measure t m fifo_reg data_sent data len =>
                     measure = word.unsigned data_sent - word.unsigned data_sent / 4 * 4
                  )
                  (Z.lt_wf 0)
                  (word.unsigned data_addr - word.unsigned data_addr / 4 * 4)).
    1: repeat straightline.
    { (* invariant holds initially: *)
      loop_simpl. reflexivity. }
    loop_simpl.
    intros measure t m0 fifo_reg' dadta_sent' data' len'. (* TODO derive names automatically *)
    repeat straightline.
    { (* if br is true, running loop body again satisfies invariant *)
      admit. }
    (* if br is false, code after loop is correct: *)
    repeat straightline.
  Admitted.

  Global Instance spec_of_hmac_sha256_final : spec_of b2_hmac_sha256_final :=
    fun function_env =>
      forall tr (m: mem) (R : mem -> Prop) (s : state)
             (input: list Byte.byte) (digest_trash: list word) (digest_addr: word),
      Z.of_nat (length digest_trash) = 8 ->
      digest_addr <> word.of_Z 0 ->
      (wordarray digest_addr digest_trash * R)%sep m ->
      execution tr (CONSUMING input) ->
      call function_env b2_hmac_sha256_final tr m [digest_addr]
        (fun tr' (m': mem) rets =>
           rets = [word.of_Z Constants.kErrorOk] /\
           execution tr' (IDLE (sha256 input) (* digest has been read, but still in device *)
                            {| hmac_done := false; (* done flag was already cleared by this function *)
                               intr_enable := word.of_Z 0;
                               hmac_en := false;
                               sha_en := true;
                               swap_endian := true;
                               swap_digest := false; |}) /\
           (* digest has been stored at correct memory location: *)
           (wordarray digest_addr (sha256 input) * R)%sep m').

  Fail Lemma hmac_sha256_final_correct :
    program_logic_goal_for_function! b2_hmac_sha256_final.
  (* bitfield_bit32_write is missing
  Proof. Qed. *)

End Proofs.
