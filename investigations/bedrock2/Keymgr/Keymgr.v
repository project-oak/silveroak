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
      out = kErrorOk
    ))).

End Impl.
