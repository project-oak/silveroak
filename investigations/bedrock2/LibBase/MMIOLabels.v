(* names for the MMIO load/store events to record in the I/O trace *)

Require Import Coq.Strings.String. Local Open Scope string_scope.

Definition READ8 := "READ8".
Definition READ16 := "READ16".
Definition READ32 := "READ32".

Definition WRITE8 := "WRITE8".
Definition WRITE16 := "WRITE16".
Definition WRITE32 := "WRITE32".
