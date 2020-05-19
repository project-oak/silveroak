Require Import Cava.Arrow.Arrow.

Require Import ArrowExamples.Nand.

(* nand previous output and current input, output delayed 1 cycle *)
Definition feedbackNand
  {Cava: CavaDelay}
  {ArrowLoop: @ArrowLoop (@cava_delay_arr Cava)}
  : bit ~> bit :=
  loopl (nand >>> uncancelr >>> delay_gate >>> copy).
