Require Import Cava.
From Coq Require Import Ascii String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition nand2Alt i01 := Cava.Inv (And2 i01).

Definition and2Alt_top := Output "o" (nand2Alt (Signal "i0", Signal "i1")).

