Require Import Cava.
From Coq Require Import Ascii String.
Require Import Coq.Lists.List.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition nand2Alt i01 := Cava.Inv (And2 i01).

Definition and2Alt_top := [Output "o" (nand2Alt (Signal "i0", Signal "i1"))].

