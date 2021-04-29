Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ToCString.
Require Import coqutil.Word.Interface.
Require Import Bedrock2Experiments.Aes.Constants.
Require Import Bedrock2Experiments.Aes.AesSemantics.
Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section Impl.
  Local Existing Instance constant_names.
  Local Existing Instance constant_vars.

  (* Notations for small constants *)
  Local Notation "0" := (expr.literal 0) (in custom bedrock_expr).
  Local Notation "1" := (expr.literal 1) (in custom bedrock_expr).
  Local Notation "2" := (expr.literal 2) (in custom bedrock_expr).
  Local Notation "3" := (expr.literal 3) (in custom bedrock_expr).
  Local Notation "4" := (expr.literal 4) (in custom bedrock_expr).
  Local Notation "5" := (expr.literal 5) (in custom bedrock_expr).
  Local Notation "6" := (expr.literal 6) (in custom bedrock_expr).
  Local Notation "7" := (expr.literal 7) (in custom bedrock_expr).
  Local Notation "8" := (expr.literal 8) (in custom bedrock_expr).
  Local Notation "9" := (expr.literal 9) (in custom bedrock_expr).

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
     (aes_globals ++ [aes_cfg_operation; aes_cfg_mode; aes_cfg_key_len;
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
  Definition aes_key_put : func :=
    let key := "key" in
    let key_len := "key_len" in
    let num_regs_key_used := "num_regs_key_used" in
    let i := "i" in
    ("b2_key_put",
     (aes_globals ++ [key; key_len], [], bedrock_func_body:(
      if (key_len == kAes256) {
        num_regs_key_used = 8
      } else {
        if (key_len == kAes192) {
          num_regs_key_used = 6
        } else {
          num_regs_key_used = 4
        }
      };

      i = 0 ;
      while (i < num_regs_key_used) {
        output! WRITE (AES_KEY0 + (i * 4), load4(key + (i * 4)));
        i = i + 1
      };

      i = num_regs_key_used ;
      while (i < AES_NUM_REGS_KEY) {
        output! WRITE (AES_KEY0 + (i * 4), 0);
        i = i + 1
      }
    ))).

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
     (aes_globals ++ [iv], [], bedrock_func_body:(
      i = 0 ;
      while (i < AES_NUM_REGS_IV) {
        output! WRITE (AES_IV0 + (i * 4), load4( iv + (i * 4) ));
        i = i + 1
      }
    ))).

  (**** aes.c
    void aes_data_put(const void *data) {
      // Write the four input data registers.
      for (int i = 0; i < AES_NUM_REGS_DATA; ++i) {
        REG32(AES_DATA_IN0(0) + i * sizeof(uint32_t)) = ((uint32_t * )data)[i];
      }
    }
   ***)
  Definition aes_data_put : func :=
    let data := "data" in
    let i := "i" in
    ("b2_data_put",
     (aes_globals ++ [data], [], bedrock_func_body:(
      i = 0 ;
      while (i < AES_NUM_REGS_DATA) {
        output! WRITE (AES_DATA_IN0 + (i * 4), load4( data + (i * 4) ));
        i = i + 1
      }
    ))).

  (**** aes.c
    void aes_data_get(void *data) {
      // Read the four output data registers.
      for (int i = 0; i < AES_NUM_REGS_DATA; ++i) {
        ((uint32_t * )data)[i] = REG32(AES_DATA_OUT0(0) + i * sizeof(uint32_t));
      }
    }
   ***)
  Definition aes_data_get : func :=
    let data := "data" in
    let val := "val" in
    let i := "i" in
    ("b2_data_get",
     (aes_globals ++ [data], [], bedrock_func_body:(
      i = 0 ;
      while (i < AES_NUM_REGS_DATA) {
        io! val = READ ( AES_DATA_OUT0 + (i * 4) ) ;
        store4( data + (i * 4), val ) ; (* data[i] = val *)
        i = i + 1
      }
    ))).

  (**** aes.c
    bool aes_data_ready(void) {
      return (REG32(AES_STATUS(0)) & (0x1u << AES_STATUS_INPUT_READY));
    }
   ***)
  Definition aes_data_ready : func :=
    let status := "status" in
    let out := "out" in
    ("b2_data_ready",
     (aes_globals ++ [], [out], bedrock_func_body:(
      io! status = READ (AES_STATUS) ;
      out = status & (1 << AES_STATUS_INPUT_READY)
    ))).

  (**** aes.c
    bool aes_data_valid(void) {
      return (REG32(AES_STATUS(0)) & (0x1u << AES_STATUS_OUTPUT_VALID));
    }
   ***)
  Definition aes_data_valid : func :=
    let status := "status" in
    let out := "out" in
    ("b2_data_valid",
     (aes_globals ++ [], [out], bedrock_func_body:(
      io! status = READ (AES_STATUS) ;
      out = status & (1 << AES_STATUS_OUTPUT_VALID)
    ))).

  (**** aes.c
    bool aes_idle(void) {
      return (REG32(AES_STATUS(0)) & (0x1u << AES_STATUS_IDLE));
    }
   ***)
  Definition aes_idle : func :=
    let status := "status" in
    let out := "out" in
    ("b2_idle",
     (aes_globals ++ [], [out], bedrock_func_body:(
      io! status = READ (AES_STATUS) ;
      out = status & (1 << AES_STATUS_IDLE)
    ))).

  (**** aes.c
    void aes_data_put_wait(const void *data) {
      // Wait for AES unit to be ready for new input data.
      while (!aes_data_ready()) {
      }

      // Provide the input data.
      aes_data_put(data);
    }
   ***)
  Definition aes_data_put_wait : func :=
    let data := "data" in
    let is_ready := "is_ready" in
    ("b2_data_put_wait",
     (aes_globals ++ [data], [], bedrock_func_body:(
      is_ready = 0 ;
      while (is_ready == 0) {
        unpack! is_ready = aes_data_ready coq:(aes_globals)
      };

      aes_data_put coq:(aes_globals ++ [expr.var data])
    ))).

  (**** aes.c

    void aes_data_get_wait(void *data) {
      // Wait for AES unit to have valid output data.
      while (!aes_data_valid()) {
      }

      // Get the data.
      aes_data_get(data);
    }
   ***)
  Definition aes_data_get_wait : func :=
    let data := "data" in
    let is_valid := "is_valid" in
    ("b2_data_get_wait",
     (aes_globals ++ [data], [], bedrock_func_body:(
      is_valid = 0 ;
      while (is_valid == 0) {
        unpack! is_valid = aes_data_valid coq:(aes_globals)
      };

      aes_data_get coq:(aes_globals ++ [expr.var data])
    ))).
End Impl.
