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

  (* Notations for small constants *)
  Local Notation "0" := (expr.literal 0) (in custom bedrock_expr).
  Local Notation "1" := (expr.literal 1) (in custom bedrock_expr).
  Local Notation "2" := (expr.literal 2) (in custom bedrock_expr).
  Local Notation "3" := (expr.literal 3) (in custom bedrock_expr).
  Local Notation "4" := (expr.literal 4) (in custom bedrock_expr).

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

  (**** aes.c
    void aes_key_put(const void *key, aes_key_len_t key_len) {
  // Determine how many key registers to use.
  size_t num_regs_key_used;
  if (key_len == kAes256) {
    num_regs_key_used = 8;
  } else if (key_len == kAes192) {
    num_regs_key_used = 6;
  } else {
    num_regs_key_used = 4;
  }

  // Write the used key registers.
  for (int i = 0; i < num_regs_key_used; ++i) {
    REG32(AES_KEY0(0) + i * sizeof(uint32_t)) = ((uint32_t * )key)[i];
  }
  // Write the unused key registers (the AES unit requires all key registers to
  // be written).
  for (int i = num_regs_key_used; i < AES_NUM_REGS_KEY; ++i) {
    REG32(AES_KEY0(0) + i * sizeof(uint32_t)) = 0x0;
  }
    }
   ***)
  (* TODO: put the enums in constants and use them!
  (* N.B. the bedrock2 version avoids the aes_key_len_t enum by taking the key
     length as a word *)
  Definition aes_key_put : func :=
    let key := "key" in
    let key_len := "key_len" in
    let num_regs_key_used := "num_regs_key_used" inb
    let i := "i" in
    ("b2_iv_put",
     (globals ++ [key; key_len], [], bedrock_func_body:(
      
      i = 0 ;
      while (i < AES_NUM_REGS_IV) {
        output! WRITE (AES_IV0 + i * 4, load4( iv + i ));
        i = i + 1
      }
    ))). *)

  (**** aes.c
    void aes_iv_put(const void *iv) {
      // Write the four initialization vector registers.
      for (int i = 0; i < AES_NUM_REGS_IV; ++i) {
        REG32(AES_IV0(0) + i * sizeof(uint32_t)) = ((uint32_t * )iv)[i];
      }
    }
   ***)
  Definition aes_iv_put : func :=
    let iv := "iv" in
    let i := "i" in
    ("b2_iv_put",
     (globals ++ [iv], [], bedrock_func_body:(
      i = 0 ;
      while (i < AES_NUM_REGS_IV) {
        output! WRITE (AES_IV0 + i * 4, load4( iv + i ));
        i = i + 1
      }
    ))).

End Impl.
