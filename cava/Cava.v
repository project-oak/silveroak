From Coq Require Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Program.Basics.

Definition inv_comb (x : bool) : bool :=
  match x with
    | true => false
    | false => true
  end.

Definition inv (x : list bool) : list bool := map inv_comb x.

Definition and2_comb (xy : bool * bool) : bool := fst xy && snd xy.

Fixpoint and2 (x : list (bool*bool)) : list bool := map and2_comb x.

Definition or2_comb (xy : (bool*bool)) : bool := fst xy || snd xy.

Fixpoint or2 (x : list (bool*bool)) : list bool := map or2_comb x.

Fixpoint delay (x : list bool) : list bool := false :: x.

Definition nand2 := compose inv and2.

Extraction Language Haskell.
Extraction "Nand2.hs" nand2.
