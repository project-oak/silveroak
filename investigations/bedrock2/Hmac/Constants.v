Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.

(* from opentitan/hw/top_earlgrey/sw/autogen/top_earlgrey.h *)
Definition TOP_EARLGREY_HMAC_BASE_ADDR := 0x41110000.

(* from opentitan/build-out/sw/device/lib/dif/libsw_dif_hmac.a.p/hmac_regs.h *)
Definition HMAC_PARAM_NUM_WORDS := 8.
Definition HMAC_PARAM_NUM_ALERTS := 1.
Definition HMAC_PARAM_REG_WIDTH := 32.
Definition HMAC_INTR_COMMON_HMAC_DONE_BIT := 0.
Definition HMAC_INTR_COMMON_FIFO_EMPTY_BIT := 1.
Definition HMAC_INTR_COMMON_HMAC_ERR_BIT := 2.
Definition HMAC_INTR_STATE_REG_OFFSET := 0x0.
Definition HMAC_INTR_STATE_HMAC_DONE_BIT := 0.
Definition HMAC_INTR_STATE_FIFO_EMPTY_BIT := 1.
Definition HMAC_INTR_STATE_HMAC_ERR_BIT := 2.
Definition HMAC_INTR_ENABLE_REG_OFFSET := 0x4.
Definition HMAC_INTR_ENABLE_HMAC_DONE_BIT := 0.
Definition HMAC_INTR_ENABLE_FIFO_EMPTY_BIT := 1.
Definition HMAC_INTR_ENABLE_HMAC_ERR_BIT := 2.
Definition HMAC_INTR_TEST_REG_OFFSET := 0x8.
Definition HMAC_INTR_TEST_HMAC_DONE_BIT := 0.
Definition HMAC_INTR_TEST_FIFO_EMPTY_BIT := 1.
Definition HMAC_INTR_TEST_HMAC_ERR_BIT := 2.
Definition HMAC_ALERT_TEST_REG_OFFSET := 0xc.
Definition HMAC_ALERT_TEST_FATAL_FAULT_BIT := 0.
Definition HMAC_CFG_REG_OFFSET := 0x10.
Definition HMAC_CFG_HMAC_EN_BIT := 0.
Definition HMAC_CFG_SHA_EN_BIT := 1.
Definition HMAC_CFG_ENDIAN_SWAP_BIT := 2.
Definition HMAC_CFG_DIGEST_SWAP_BIT := 3.
Definition HMAC_CMD_REG_OFFSET := 0x14.
Definition HMAC_CMD_HASH_START_BIT := 0.
Definition HMAC_CMD_HASH_PROCESS_BIT := 1.
Definition HMAC_STATUS_REG_OFFSET := 0x18.
Definition HMAC_STATUS_FIFO_EMPTY_BIT := 0.
Definition HMAC_STATUS_FIFO_FULL_BIT := 1.
Definition HMAC_STATUS_FIFO_DEPTH_MASK := 0x1f.
Definition HMAC_STATUS_FIFO_DEPTH_OFFSET := 4.
Definition HMAC_ERR_CODE_REG_OFFSET := 0x1c.
Definition HMAC_WIPE_SECRET_REG_OFFSET := 0x20.
Definition HMAC_KEY_KEY_FIELD_WIDTH := 32.
Definition HMAC_KEY_KEY_FIELDS_PER_REG := 1.
Definition HMAC_KEY_MULTIREG_COUNT := 8.
Definition HMAC_KEY_0_REG_OFFSET := 0x24.
Definition HMAC_KEY_1_REG_OFFSET := 0x28.
Definition HMAC_KEY_2_REG_OFFSET := 0x2c.
Definition HMAC_KEY_3_REG_OFFSET := 0x30.
Definition HMAC_KEY_4_REG_OFFSET := 0x34.
Definition HMAC_KEY_5_REG_OFFSET := 0x38.
Definition HMAC_KEY_6_REG_OFFSET := 0x3c.
Definition HMAC_KEY_7_REG_OFFSET := 0x40.
Definition HMAC_DIGEST_DIGEST_FIELD_WIDTH := 32.
Definition HMAC_DIGEST_DIGEST_FIELDS_PER_REG := 1.
Definition HMAC_DIGEST_MULTIREG_COUNT := 8.
Definition HMAC_DIGEST_0_REG_OFFSET := 0x44.
Definition HMAC_DIGEST_1_REG_OFFSET := 0x48.
Definition HMAC_DIGEST_2_REG_OFFSET := 0x4c.
Definition HMAC_DIGEST_3_REG_OFFSET := 0x50.
Definition HMAC_DIGEST_4_REG_OFFSET := 0x54.
Definition HMAC_DIGEST_5_REG_OFFSET := 0x58.
Definition HMAC_DIGEST_6_REG_OFFSET := 0x5c.
Definition HMAC_DIGEST_7_REG_OFFSET := 0x60.
Definition HMAC_MSG_LENGTH_LOWER_REG_OFFSET := 0x64.
Definition HMAC_MSG_LENGTH_UPPER_REG_OFFSET := 0x68.
Definition HMAC_MSG_FIFO_REG_OFFSET := 0x800.
Definition HMAC_MSG_FIFO_SIZE_WORDS := 512.
Definition HMAC_MSG_FIFO_SIZE_BYTES := 2048.

(* from opentitan/sw/device/silicon_creator/lib/absl_status.h *)
Definition kOk := 0.
Definition kCancelled := 1.
Definition kUnknown := 2.
Definition kInvalidArgument := 3.
Definition kDeadlineExceeded := 4.
Definition kNotFound := 5.
Definition kAlreadyExists := 6.
Definition kPermissionDenied := 7.
Definition kResourceExhausted := 8.
Definition kFailedPrecondition := 9.
Definition kAborted := 10.
Definition kOutOfRange := 11.
Definition kUnimplemented := 12.
Definition kInternal := 13.
Definition kUnavailable := 14.
Definition kDataLoss := 15.
Definition kUnauthenticated := 16.

(* from opentitan/sw/device/silicon_creator/lib/error.h *)
Definition kModuleUnknown := 0.
Definition kModuleAlertHandler := 0x4148.
Definition kModuleUart := 0x4155.
Definition kModuleHmac := 0x4d48.
Definition kModuleSigverify := 0x5653.
Definition kModuleKeymgr := 0x4d4b.
Definition kModuleManifest := 0x414d.
Definition kModuleRomextimage := 0x4552.
Definition ERROR_(error_ module_ status_: Z): Z :=
  Z.lor (Z.shiftl error_ 24) (Z.lor (Z.shiftl module_ 8) status_).
Definition kErrorOk := 0x739.
Definition kErrorUartInvalidArgument :=        ERROR_ 1 kModuleUart kInvalidArgument.
Definition kErrorUartBadBaudRate :=            ERROR_ 2 kModuleUart kInvalidArgument.
Definition kErrorHmacInvalidArgument :=        ERROR_ 1 kModuleHmac kInvalidArgument.
Definition kErrorSigverifyInvalidArgument :=   ERROR_ 1 kModuleSigverify kInvalidArgument.
Definition kErrorKeymgrInternal :=             ERROR_ 1 kModuleKeymgr kInternal.
Definition kErrorManifestInternal :=           ERROR_ 1 kModuleManifest kInternal.
Definition kErrorRomextimageInvalidArgument := ERROR_ 1 kModuleRomextimage kInvalidArgument.
Definition kErrorRomextimageInternal :=        ERROR_ 2 kModuleRomextimage kInternal.
Definition kErrorAlertBadIndex :=              ERROR_ 1 kModuleAlertHandler kInvalidArgument.
Definition kErrorAlertBadClass :=              ERROR_ 2 kModuleAlertHandler kInvalidArgument.
Definition kErrorAlertBadEnable :=             ERROR_ 3 kModuleAlertHandler kInvalidArgument.
Definition kErrorAlertBadEscalation :=         ERROR_ 4 kModuleAlertHandler kInvalidArgument.
Definition kErrorUnknown := 0xFFFFFFFF.
