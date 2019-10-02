Require Import Cava.
From Coq Require Import Ascii String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Basics.
Local Open Scope program_scope.

Definition nand2_pipelined := Delay ∘ Inv ∘ Delay ∘ And2.

Definition and2_pipelined_top
  := Output "o" (nand2_pipelined (Signal "i0", Signal "i1")).

