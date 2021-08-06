Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.

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
