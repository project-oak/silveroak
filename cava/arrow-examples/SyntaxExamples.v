Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Lists.Streams.

Import ListNotations.

From Coq Require Import ZArith.
From Coq Require Import btauto.Btauto.

Require Import Cava.Netlist.

Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Kappa.Syntax.
Require Import Cava.Arrow.Instances.Combinational.
Require Import Cava.Arrow.Instances.Netlist.

Open Scope source.

Definition xilinxFullAdder
  : Kappa (bit ** (bit ** bit) ** unit) (bit**bit) :=
  <[ \ cin ab =>
     let a = fst' ab in
     let b = snd' ab in
     let part_sum = !xor_gate a b in
     let sum      = !xorcy part_sum cin in
     let cout     = !muxcy part_sum (cin, a) in
     (sum, cout)
  ]>.

Definition xilinxFullAdder' := Closure_conversion xilinxFullAdder.

