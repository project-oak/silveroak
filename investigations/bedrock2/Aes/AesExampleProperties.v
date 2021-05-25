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
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.StateMachineProperties.
Require Import Bedrock2Experiments.Tactics.
Require Import Bedrock2Experiments.Word.
Require Import Bedrock2Experiments.WordProperties.
Require Import Bedrock2Experiments.Aes.Aes.
Require Import Bedrock2Experiments.Aes.AesExample.
Require Import Bedrock2Experiments.Aes.AesSemantics.
Require Import Bedrock2Experiments.Aes.AesProperties.
Require Import Bedrock2Experiments.Aes.Constants.
Import Syntax.Coercions List.ListNotations.
Local Open Scope Z_scope.

Section Proofs.
  Context {p : AesSemantics.parameters} {p_ok : parameters.ok p}
          {consts : aes_constants Z} {timing : timing}.
  Context {consts_ok : aes_constants_ok constant_words}.
  Existing Instance constant_words.
  Existing Instance state_machine_parameters.

  Instance spec_of_aes_encrypt : spec_of aes_encrypt :=
    fun function_env =>
      forall (tr : trace) (m : mem) R
        (plaintext_ptr key_ptr iv_ptr ciphertext_ptr : Semantics.word)
        (* values of input arrays *)
        (plaintext0 plaintext1 plaintext2 plaintext3
                    key0 key1 key2 key3 key4 key5 key6 key7
                    iv0 iv1 iv2 iv3 : Semantics.word)
        (* initial values of output array (used only for determining length) *)
        (ciphertext_arr : list Semantics.word)
        (s : state),
        let plaintext_arr := [plaintext0; plaintext1; plaintext2; plaintext3] in
        let key_arr := [key0; key1; key2; key3; key4; key5; key6; key7] in
        let iv_arr := [iv0; iv1; iv2; iv3] in
        (* arrays are in memory *)
        (array scalar32 (word.of_Z 4) plaintext_ptr plaintext_arr
         * array scalar32 (word.of_Z 4) key_ptr key_arr
         * array scalar32 (word.of_Z 4) iv_ptr iv_arr
         * array scalar32 (word.of_Z 4) ciphertext_ptr ciphertext_arr
         * R)%sep m ->
        (* output array has the right length *)
        length ciphertext_arr = 4%nat ->
        (* circuit must start in the UNINITIALIZED state *)
        execution (p:=state_machine_parameters) tr UNINITIALIZED ->
        (* determine expected output using aes_spec *)
        let is_decrypt := false in
        let expected_output :=
            parameters.aes_spec
              is_decrypt
              (key0, key1, key2, key3, key4, key5, key6, key7)
              (iv0, iv1, iv2, iv3)
              (plaintext0, plaintext1, plaintext2, plaintext3) in
        let args := [plaintext_ptr; key_ptr; iv_ptr; ciphertext_ptr] in
        call function_env aes_encrypt tr m (aes_globals ++ args)
             (fun tr' m' rets =>
                let '(out0, out1, out2, out3) := expected_output in
                (* the circuit is back in the IDLE state *)
                (exists data, execution (p:=state_machine_parameters) tr' (IDLE data))
                (* ...and the input arrays are unchanged, while the ciphertext
                     array now holds the values from the expected output *)
                /\ (array scalar32 (word.of_Z 4) plaintext_ptr plaintext_arr
                   * array scalar32 (word.of_Z 4) iv_ptr iv_arr
                   * array scalar32 (word.of_Z 4) key_ptr key_arr
                   * array scalar32 (word.of_Z 4) ciphertext_ptr
                           [out0; out1; out2; out3] * R)%sep m'
                (* ...and there are no return values *)
                /\ rets = []).

  Local Ltac precondition_hammer :=
    lazymatch goal with
    | |- enum_member ?e _ => cbv [enum_member]; cbn [In]; tauto
    | |- boolean _ => cbv [boolean]; tauto
    | |- execution _ _ => eassumption
    | |- output_matches_state _ _ => reflexivity
    | H : sep _ _ ?m |- _ ?m => ecancel_assumption
    | _ => try reflexivity
    end.

  Lemma aes_encrypt_correct :
    program_logic_goal_for_function! aes_encrypt.
  Proof.

    (* initial processing *)
    repeat straightline.
    destruct_lists_by_length.

    (* call aes_init *)
    straightline_call; precondition_hammer; [ ].
    change AES_CTRL with (reg_addr CTRL) in *.
    repeat straightline.

    (* call aes_key_put *)
    straightline_call; precondition_hammer; [ | ].
    { (* prove key array has the correct length *)
      pose proof (enum_unique aes_key_len) as Hunique.
      simplify_unique_words_in Hunique.
      cbn [constant_words kAes256 kAes128 kAes192].
      change Semantics.width with 32.
      change Semantics.word with parameters.word.
      repeat destruct_one_match; subst; try congruence; [ ].
      reflexivity. }

    repeat straightline.
    lazymatch goal with
    | H : execution ?t _ |- context [?t] =>
      cbn in H
    end.

    (* call aes_iv_put *)
    straightline_call; precondition_hammer; [ ].
    repeat straightline.
    lazymatch goal with
    | H : execution ?t _ |- context [?t] =>
      cbn in H
    end.

    (* call aes_data_put_wait *)
    straightline_call; precondition_hammer; [ ].
    repeat straightline.
    lazymatch goal with
    | H : execution ?t _ |- context [?t] =>
      cbn in H
    end.
    repeat lazymatch goal with
           | H : context [match ?p with pair _ _ => _ end] |- _ =>
             rewrite (surjective_pairing p) in H
           end.

    (* call aes_data_get_wait *)
    straightline_call; precondition_hammer; [ ].
    repeat straightline.

    (* done; prove postcondition *)
    repeat destruct_pair_let.
    ssplit; eauto; [ ].
    repeat lazymatch goal with H : execution _ _ |- _ => clear H end.
    cbn [busy_exp_output data_out0 data_out1 data_out2 data_out3] in *.
    lazymatch goal with
    | Hsep : sep _ _ ?m |- sep _ _ ?m =>
      lazymatch type of Hsep with
        context [parameters.aes_spec ?op ?keys ?iv ?plaintext] =>
        replace (parameters.aes_spec op keys iv plaintext)
        with expected_output in Hsep
      end
    end; [ ecancel_assumption | ].
    subst_lets. f_equal; [ ].
    lazymatch goal with
    | H : ctrl_operation _ = _ |- _ =>
      cbv [ctrl_operation] in H;
        cbn [AES_CTRL_OPERATION constant_words] in H;
        rewrite H
    end.
    rewrite word.unsigned_eqb.
    rewrite kAesEnc_eq. push_unsigned.
    cbn [Z.eqb negb]. reflexivity.
  Qed.
End Proofs.
