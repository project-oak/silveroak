Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import coqutil.Word.Interface.
Require Import Bedrock2Experiments.Aes.Aes.
Require Import Bedrock2Experiments.Aes.Constants.
Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(**** Usage example for AES firmware functions + proof; checks that proofs
      compose properly ****)

Section Impl.
  Local Existing Instance constant_names.
  Local Existing Instance constant_vars.

  (* Notations for small constants *)
  Local Notation "0" := (expr.literal 0) (in custom bedrock_expr).

  Definition aes_encrypt : func :=
    let plaintext := "plaintext" in
    let key := "key" in
    let iv := "iv" in
    let ciphertext := "ciphertext" in
    ("b2_aes_encrypt",
     ([AES_CTRL; AES_CTRL_OPERATION;
      AES_CTRL_MODE_MASK; AES_CTRL_MODE_OFFSET; AES_CTRL_KEY_LEN_MASK;
      AES_CTRL_KEY_LEN_OFFSET; AES_CTRL_MANUAL_OPERATION; kAesEnc; kAesEcb;
      AES_KEY0; AES_NUM_REGS_KEY; kAes256; kAes192;
      AES_IV0; AES_NUM_REGS_IV;
      AES_DATA_IN0; AES_NUM_REGS_DATA;
      AES_STATUS; AES_STATUS_INPUT_READY;
      AES_DATA_OUT0; AES_STATUS_OUTPUT_VALID;
      plaintext; key; iv; ciphertext], [], bedrock_func_body:(
       (* initialize the AES block :
          operation = kAesEnc, mode = kAesEcb, key_len = kAes256,
          manual_operation = 0 *)
       aes_init (AES_CTRL, AES_CTRL_OPERATION, AES_CTRL_MODE_MASK,
                 AES_CTRL_MODE_OFFSET, AES_CTRL_KEY_LEN_MASK,
                 AES_CTRL_KEY_LEN_OFFSET, AES_CTRL_MANUAL_OPERATION,
                 kAesEnc, kAesEcb, kAes256, 0) ;

       (* write key and initialization vector *)
       aes_key_put (AES_KEY0, AES_NUM_REGS_KEY, kAes256, kAes192, key, kAes256) ;
       aes_iv_put (AES_IV0, AES_NUM_REGS_IV, iv) ;

       (* write input data *)
       aes_data_put_wait (AES_DATA_IN0, AES_NUM_REGS_DATA, AES_STATUS,
                          AES_STATUS_INPUT_READY, plaintext) ;

       (* wait for output, write it to ciphertext *)
       aes_data_get_wait (AES_DATA_OUT0, AES_NUM_REGS_DATA, AES_STATUS,
                          AES_STATUS_OUTPUT_VALID, ciphertext)
    ))).
End Impl.
