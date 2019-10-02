From Top Require Import Cava.
Require Import Nand2.
Require Import OneBitAdder.
From Coq Require Import Extraction.

Extraction Language Haskell.

Recursive Extraction Library Cava.
Extraction Library Nand2.
Extraction Library OneBitAdder.
(* Separate Extraction Nand2. *)