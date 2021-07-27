Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Local Open Scope string_scope.

Definition INCR_BASE_ADDR: Z := 16 * 2^10.
Definition VALUE_ADDR: Z := INCR_BASE_ADDR.
Definition STATUS_ADDR: Z := INCR_BASE_ADDR + 4.
Definition INCR_END_ADDR: Z := INCR_BASE_ADDR + 8.

Definition STATUS_IDLE: Z := 0.
Definition STATUS_BUSY: Z := 1.
Definition STATUS_DONE: Z := 2.
