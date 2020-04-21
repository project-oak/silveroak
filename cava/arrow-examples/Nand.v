Require Import Cava.Arrow.Arrow.

(* Implement a NAND circuit by composing an AND gate and INV gate. *)
Definition nand
  `{Cava}
  := and_gate >>> not_gate.
