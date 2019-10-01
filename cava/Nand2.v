Require Import Cava.
From Coq Require Import Ascii String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Basics.
Local Open Scope program_scope.

Definition nand2Alt := Delay ∘ Inv ∘ Delay ∘ And2.

Definition and2Alt_top := Output "o" (nand2Alt (Signal "i0", Signal "i1")).

