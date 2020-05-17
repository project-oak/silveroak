Require Import Cava.Arrow.Arrow.

(* Implement a NAND circuit by composing an AND gate and INV gate. *)
Definition nand
  `{Cava}
  := second uncancelr >>> and_gate >>> uncancelr >>> not_gate.
