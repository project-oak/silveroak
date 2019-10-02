Require Import Cava.
From Coq Require Import Ascii String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Basics.
Local Open Scope program_scope.

Definition oneBitAdder (a b cin : cava) : cava * cava
  := let partSum := Xor2 (a, b) in
     let sum := Xorcy (partSum, cin) in
     let cout := Muxcy (partSum, a, cin) in
       (sum, cout).