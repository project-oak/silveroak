# Cava: Lava-style circuits in Coq

This is a work in progress attempt to encode Lava-style gate-level circuit descriptions
in Coq for circuit specification, formal verification and extraction into VHDL or
Verilog for implementation on FPGAs.

Currently circuits are modelled as operations over lists of boolean values. It probably
makes more sense to use the Stream library of Coq. From the file [Cava.v](Cava.v)

```coq
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

```

The extracted Haskell for the nand2 gate is:

```haskell
module Nand2 where

import qualified Prelude

data Bool =
   True
 | False

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

data Prod a b =
   Pair a b

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x _ -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair _ y -> y}

data List a =
   Nil
 | Cons a (List a)

compose :: (a2 -> a3) -> (a1 -> a2) -> a1 -> a3
compose g f x =
  g (f x)

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

inv_comb :: Bool -> Bool
inv_comb x =
  case x of {
   True -> False;
   False -> True}

inv :: (List Bool) -> List Bool
inv x =
  map inv_comb x

and2_comb :: (Prod Bool Bool) -> Bool
and2_comb xy =
  andb (fst xy) (snd xy)

and2 :: (List (Prod Bool Bool)) -> List Bool
and2 x =
  map and2_comb x

nand2 :: (List (Prod Bool Bool)) -> List Bool
nand2 =
  compose inv and2
```

