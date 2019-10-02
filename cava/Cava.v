From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
From Coq Require Import Program.Basics.
Local Open Scope program_scope.
From Coq Require Extraction.

(*** Various experiments for representing synchronous gate-level
     circuits in Coq in a Lava-style.
***)

(* A deep embeding with a data structure that represents Cava circuit
   expressions.
*)

Inductive cava : Set :=
  | Inv : cava -> cava
  | And2 : cava * cava -> cava
  | Or2 : cava * cava -> cava
  | Xor2 : cava * cava -> cava
  | Delay : cava -> cava
  | Signal : string -> cava
  | Output : string -> cava -> cava.

(* A list-based semantics for gate level elements. We could also
   use streams.
*)

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

Definition nand2 := inv ∘ and2.

