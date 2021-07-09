Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Local Open Scope string_scope.

(* read and write interaction names *)
Definition READ := "MMIOREAD".
Definition WRITE := "MMIOWRITE".

Definition VALUE_ADDR: Z := 16 * 2^10.
Definition STATUS_ADDR: Z := 16 * 2^10.
