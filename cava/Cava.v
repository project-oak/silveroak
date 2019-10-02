From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
From Coq Require Import Program.Basics.
Local Open Scope program_scope.
From Coq Require Import Extraction.

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
  | Xorcy : cava * cava -> cava
  | Muxcy : cava * cava * cava -> cava
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

Definition and2_comb (xy : bool*bool) : bool := fst xy && snd xy.
Fixpoint and2 (x y : list bool) : list bool := map and2_comb (combine x y).

Definition or2_comb (xy : bool*bool) : bool := fst xy || snd xy.
Fixpoint or2 (x y : list bool) : list bool := map or2_comb (combine x y).

Definition xor2_comb (xy : bool*bool) : bool := xorb (fst xy) (snd xy).
Fixpoint xor2 (x y : list bool) : list bool := map or2_comb (combine x y).

Definition xorcy := xor2.

Definition muxcy_comb (cidis : bool*bool*bool) : bool
  := let '(ci, di, s) := cidis
     in if s then
          di
        else
          ci.
Fixpoint muxcy (ci di s : list bool) : list bool
  := map muxcy_comb (combine (combine ci di) s).

Fixpoint delay (x : list bool) : list bool := false :: x.



