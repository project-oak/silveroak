Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ToCString.
Require Import coqutil.Word.Interface.
Require Import Bedrock2Experiments.Aes.AesSemantics.
Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section Impl.
  Import constants.
  Local Existing Instance constant_names.
  Local Existing Instance constant_vars.

  (**** aes.c
    void aes_init(aes_cfg_t aes_cfg) {
      REG32(AES_CTRL(0)) =
          (aes_cfg.operation << AES_CTRL_OPERATION) |
          ((aes_cfg.mode & AES_CTRL_MODE_MASK) << AES_CTRL_MODE_OFFSET) |
          ((aes_cfg.key_len & AES_CTRL_KEY_LEN_MASK) << AES_CTRL_KEY_LEN_OFFSET) |
          (aes_cfg.manual_operation << AES_CTRL_MANUAL_OPERATION);
    };
   ***)
  Definition aes_init : func :=
    let aes_cfg_operation := "aes_cfg_operation" in
    let aes_cfg_mode := "aes_cfg_mode" in
    let aes_cfg_key_len := "aes_cfg_key_len" in
    let aes_cfg_manual_operation := "aes_cfg_manual_operation" in
    let cfg_val := "cfg_val" in
    ("b2_aes_init",
     (globals ++ [aes_cfg_operation; aes_cfg_mode; aes_cfg_key_len;
                 aes_cfg_manual_operation],
      [], bedrock_func_body:(
      output! WRITE (AES_CTRL,
                     ((aes_cfg_operation << AES_CTRL_OPERATION) |
                      ((aes_cfg_mode & AES_CTRL_MODE_MASK)
                         << AES_CTRL_MODE_OFFSET) |
                      ((aes_cfg_key_len & AES_CTRL_KEY_LEN_MASK)
                         << AES_CTRL_KEY_LEN_OFFSET) |
                      (aes_cfg_manual_operation << AES_CTRL_MANUAL_OPERATION)))
    ))).
End Impl.
