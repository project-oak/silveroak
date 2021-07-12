Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Local Open Scope string_scope.

(* read and write interaction names *)
Definition READ := "MMIOREAD".
Definition WRITE := "MMIOWRITE".

Definition VALUE_ADDR: Z := 16 * 2^10.
Definition STATUS_ADDR: Z := 16 * 2^10 + 4.

Definition STATUS_IDLE: Z := 0.
Definition STATUS_BUSY: Z := 1.
Definition STATUS_DONE: Z := 2.

