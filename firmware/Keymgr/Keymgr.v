Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ToCString.
Require Import coqutil.Word.Interface.
Require Import Bedrock2Experiments.Keymgr.Constants.
Require Import Bedrock2Experiments.LibBase.AbsMMIO.
Require Import Bedrock2Experiments.LibBase.Bitfield.
Require Import Bedrock2Experiments.LibBase.Constants.

Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section Impl.
  Local Notation "0" := (expr.literal 0) (in custom bedrock_expr).
  Local Notation "1" := (expr.literal 1) (in custom bedrock_expr).

  (****
    static rom_error_t check_expected_state(uint32_t expected_state,
                                           uint32_t expected_status) {
      // Read and clear the status register by writing back the read value,
      // polling until the status is non-WIP.
      uint32_t op_status;
      uint32_t op_status_field;
      do {
        op_status = abs_mmio_read32(kBase + KEYMGR_OP_STATUS_REG_OFFSET);
        abs_mmio_write32(kBase + KEYMGR_OP_STATUS_REG_OFFSET, op_status);
        op_status_field =
        bitfield_field32_read(op_status, KEYMGR_OP_STATUS_STATUS_FIELD);
      } while (op_status_field == KEYMGR_OP_STATUS_STATUS_VALUE_WIP);

      // Read and clear the error register by writing back the read value.
      uint32_t error_code = abs_mmio_read32(kBase + KEYMGR_ERR_CODE_REG_OFFSET);
      abs_mmio_write32(kBase + KEYMGR_ERR_CODE_REG_OFFSET, error_code);

      uint32_t got_state = abs_mmio_read32(kBase + KEYMGR_WORKING_STATE_REG_OFFSET);
      if (op_status_field == expected_status && error_code == 0u &&
        got_state == expected_state) {
        return kErrorOk;
      }
      return kErrorKeymgrInternal;
    }
   ***)
  Definition check_expected_state : func :=
    let expected_state := "expected_state" in
    let expected_status := "expected_status" in
    let op_status := "op_status" in
    let op_status_field := "op_status_field" in
    let error_code := "error_code" in
    let got_state := "got_state" in
    let out := "out" in
    ("b2_check_expected_state", ([expected_state; expected_status], [out],
    bedrock_func_body:(
      unpack! op_status = abs_mmio_read32(TOP_EARLGREY_KEYMGR_BASE_ADDR + KEYMGR_OP_STATUS_REG_OFFSET);
      abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR + KEYMGR_OP_STATUS_REG_OFFSET, op_status);
      unpack! op_status_field = bitfield_field32_read(op_status, KEYMGR_OP_STATUS_STATUS_MASK, KEYMGR_OP_STATUS_STATUS_OFFSET);
      while (op_status_field == KEYMGR_OP_STATUS_STATUS_VALUE_WIP) {
        unpack! op_status = abs_mmio_read32(TOP_EARLGREY_KEYMGR_BASE_ADDR + KEYMGR_OP_STATUS_REG_OFFSET);
        abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR + KEYMGR_OP_STATUS_REG_OFFSET, op_status);
        unpack! op_status_field = bitfield_field32_read(op_status, KEYMGR_OP_STATUS_STATUS_MASK, KEYMGR_OP_STATUS_STATUS_OFFSET)
      };
      unpack! error_code = abs_mmio_read32(TOP_EARLGREY_KEYMGR_BASE_ADDR + KEYMGR_ERR_CODE_REG_OFFSET);
      abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR + KEYMGR_ERR_CODE_REG_OFFSET, error_code);
      unpack! got_state = abs_mmio_read32(TOP_EARLGREY_KEYMGR_BASE_ADDR + KEYMGR_WORKING_STATE_REG_OFFSET);
    if ((op_status_field == expected_status)
         & (error_code == 0)
         & (got_state == expected_state)) {
       out = kErrorOk
     } else {
       out = kErrorKeymgrInternal
     }
    ))).

  (****
    static void advance_state(void) {
      uint32_t reg = bitfield_bit32_write(0, KEYMGR_CONTROL_START_BIT, true);
      reg = bitfield_field32_write(reg, KEYMGR_CONTROL_DEST_SEL_FIELD,
                              KEYMGR_CONTROL_DEST_SEL_VALUE_NONE);
      reg = bitfield_field32_write(reg, KEYMGR_CONTROL_OPERATION_FIELD,
                              KEYMGR_CONTROL_OPERATION_VALUE_ADVANCE);
      abs_mmio_write32(kBase + KEYMGR_CONTROL_REG_OFFSET, reg);
    }
   ***)
  Definition advance_state : func :=
    let reg := "reg" in
    ("b2_advance_state", ([], [],
    bedrock_func_body:(
      unpack! reg = bitfield_bit32_write(0, KEYMGR_CONTROL_START_BIT, 1);
      unpack! reg = bitfield_field32_write(reg, KEYMGR_CONTROL_DEST_SEL_MASK,
                                           KEYMGR_CONTROL_DEST_SEL_OFFSET,
                                           KEYMGR_CONTROL_DEST_SEL_VALUE_NONE);
      unpack! reg = bitfield_field32_write(reg, KEYMGR_CONTROL_OPERATION_MASK,
                                           KEYMGR_CONTROL_OPERATION_OFFSET,
                                           KEYMGR_CONTROL_OPERATION_VALUE_ADVANCE);
      abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR + KEYMGR_CONTROL_REG_OFFSET, reg)
    ))).

  (****
    rom_error_t keymgr_init(uint16_t entropy_reseed_interval) {
      RETURN_IF_ERROR(check_expected_state(KEYMGR_WORKING_STATE_STATE_VALUE_RESET,
                                           KEYMGR_OP_STATUS_STATUS_VALUE_IDLE));

      uint32_t reg = bitfield_field32_write(0, KEYMGR_RESEED_INTERVAL_VAL_FIELD,
                                            entropy_reseed_interval);
      abs_mmio_write32(kBase + KEYMGR_RESEED_INTERVAL_REG_OFFSET, reg);

      // Advance to INIT state.
      advance_state();
      return kErrorOk;
    }
   ***)
  Definition keymgr_init : func :=
    let reg := "reg" in
    let err := "err" in
    let entropy_reseed_interval := "entropy_reseed_interval" in
    let out := "out" in
    ("b2_keymgr_init", ([entropy_reseed_interval], [out],
    bedrock_func_body:(
      unpack! err = check_expected_state(KEYMGR_WORKING_STATE_STATE_VALUE_RESET,
                                         KEYMGR_OP_STATUS_STATUS_VALUE_IDLE);
      if (err == kErrorOk) {
        unpack! reg = bitfield_field32_write(0, KEYMGR_RESEED_INTERVAL_VAL_MASK,
                                             KEYMGR_RESEED_INTERVAL_VAL_OFFSET,
                                             entropy_reseed_interval);
        abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR + KEYMGR_RESEED_INTERVAL_REG_OFFSET, reg);
        advance_state();
        out = kErrorOk

      } else {
        out = err
             }
    ))).

  (****
    rom_error_t keymgr_state_advance_to_creator(const uint32_t binding_value[8],
                                                uint32_t max_key_ver) {
      RETURN_IF_ERROR(
          check_expected_state(KEYMGR_WORKING_STATE_STATE_VALUE_INIT,
                               KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS));

      // Write and lock (rw0c) the software binding value. This register is unlocked
      // by hardware upon a successful state transition.
      // FIXME: Consider using sec_mmio module for the following register writes.
      for (size_t i = 0; i < 8; ++i) {
        abs_mmio_write32(
            kBase + KEYMGR_SW_BINDING_0_REG_OFFSET + i * sizeof(uint32_t),
            binding_value[i]);
      }
      abs_mmio_write32(kBase + KEYMGR_SW_BINDING_REGWEN_REG_OFFSET, 0);

      // Write and lock (rw0c) the max key version.
      abs_mmio_write32(kBase + KEYMGR_MAX_CREATOR_KEY_VER_REG_OFFSET, max_key_ver);
      abs_mmio_write32(kBase + KEYMGR_MAX_CREATOR_KEY_VER_REGWEN_REG_OFFSET, 0);

      // Advance to CREATOR_ROOT_KEY state.
      advance_state();
      return kErrorOk;
    }
   ***)
  (* Note: unrolling the loop/array might be easier to reason *)
  Definition keymgr_state_advance_to_creator : func :=
    let err := "err" in
    let binding_value_0 := "binding_value_0" in
    let binding_value_1 := "binding_value_1" in
    let binding_value_2 := "binding_value_2" in
    let binding_value_3 := "binding_value_3" in
    let binding_value_4 := "binding_value_4" in
    let binding_value_5 := "binding_value_5" in
    let binding_value_6 := "binding_value_6" in
    let binding_value_7 := "binding_value_7" in
    let max_key_ver := "max_key_ver" in
    let out := "out" in
    ("b2_keymgr_state_advance_to_creator", ([binding_value_0; binding_value_1;
    binding_value_2; binding_value_3; binding_value_4; binding_value_5;
    binding_value_6; binding_value_7; max_key_ver], [out],
    bedrock_func_body:(
      unpack! err = check_expected_state(KEYMGR_WORKING_STATE_STATE_VALUE_INIT,
                                         KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);
      if (err == kErrorOk) {
        abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR+KEYMGR_SW_BINDING_0_REG_OFFSET, binding_value_0);
        abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR+KEYMGR_SW_BINDING_1_REG_OFFSET, binding_value_1);
        abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR+KEYMGR_SW_BINDING_2_REG_OFFSET, binding_value_2);
        abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR+KEYMGR_SW_BINDING_3_REG_OFFSET, binding_value_3);
        abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR+KEYMGR_SW_BINDING_4_REG_OFFSET, binding_value_4);
        abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR+KEYMGR_SW_BINDING_5_REG_OFFSET, binding_value_5);
        abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR+KEYMGR_SW_BINDING_6_REG_OFFSET, binding_value_6);
        abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR+KEYMGR_SW_BINDING_7_REG_OFFSET, binding_value_7);

        abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR+KEYMGR_SW_BINDING_REGWEN_REG_OFFSET, 0);
        abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR+KEYMGR_MAX_CREATOR_KEY_VER_REG_OFFSET, max_key_ver);
        abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR+KEYMGR_MAX_CREATOR_KEY_VER_REGWEN_REG_OFFSET, 0);
        advance_state();
        out = kErrorOk
      } else {
        out = err
      }
    ))).

  (****
    rom_error_t keymgr_state_creator_check() {
      return check_expected_state(KEYMGR_WORKING_STATE_STATE_VALUE_CREATOR_ROOT_KEY,
                                  KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);
    }
   ***)
  Definition keymgr_state_creator_check : func :=
    let out := "out" in
    ("b2_keymgr_state_creator_check", ([], [out],
    bedrock_func_body:(
      unpack! out = check_expected_state(KEYMGR_WORKING_STATE_STATE_VALUE_CREATOR_ROOT_KEY,
                                 KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS)
    ))).
End Impl.
