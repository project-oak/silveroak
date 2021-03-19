(****************************************************************************)
(* Copyright 2020 The Project Oak Authors                                   *)
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License")           *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(*     http://www.apache.org/licenses/LICENSE-2.0                           *)
(*                                                                          *)
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Monads.
Require Import Cava.Core.Core.
Require Import Cava.Util.Vector.
Require Cava.Lib.Vec.
Import ListNotations MonadNotation.
Local Open Scope monad_scope.

(**** IMPORTANT: if you make changes to the API of these definitions, or add new
      ones, make sure you update the reference at docs/reference.md! ****)

(****************************************************************************)
(* Lava-style circuit combinators.                                          *)
(****************************************************************************)

Section WithCava.
  Context {signal} {semantics: Cava signal}.
  Existing Instance monad. (* make sure cava Monad instance takes precedence *)

  (****************************************************************************)
  (* Forks in wires                                                           *)
  (****************************************************************************)

  (* forks a wire into two *)
  Definition fork2 {A} (a:A) := ret (a, a).

  (****************************************************************************)
  (* Operations over pairs.                                                   *)
  (****************************************************************************)

  (* applies f to the first element of a pair *)
  Definition first {A B C} (f : A -> cava C) (ab : A * B) : cava (C * B) :=
    let '(a, b) := ab in
    c <- f a ;;
    ret (c, b).

  (* applies f to the second element of a pair *)
  Definition second {A B C} (f : B -> cava C) (ab : A * B) : cava (A * C) :=
    let '(a, b) := ab in
    c <- f b ;;
    ret (a, c).

  (* reverses elements of a pair *)
  Definition swap {A B} (i : A * B) : cava (B * A) :=
    let (a, b) := i in
    ret (b, a).

  (* drops right element of a pair *)
  Definition dropr {A B} (i : A * B) : cava A :=
    ret (fst i).

  (* drops left element of a pair *)
  Definition dropl {A B} (i : A * B) : cava B :=
    ret (snd i).

  (* pair_left takes an input with shape (a, (b, c)) and re-organizes
      it as ((a, b), c) *)
  Definition pair_left {A B C} (i : A * (B * C)) : cava (A * B * C) :=
   let '(a, (b, c)) := i in
   ret (a, b, c).

  (* pair_right takes an input with shape ((a, b), c) and re-organizes
     it as (a, (b, c)) *)
  Definition pair_right {A B C} (i : A * B * C) : cava (A * (B * C)) :=
   let '(a, b, c) := i in
   ret (a, (b, c)).

  (****************************************************************************)
  (* 4-sided tile combinators                                                 *)
  (****************************************************************************)

  (* Below combinator

  -----------------------------------------------------------------------------
  -- Below
  -----------------------------------------------------------------------------
  -- below r s
  --            ^
  --            |
  --            f
  --            ^
  --            |
  --          -----
  --         |     |
  --     c ->|  s  |-> e
  --         |     |
  --          -----
  --            ^
  --            |
  --            g
  --            ^
  --            |
  --          -----
  --         |     |
  --     b ->|  r  |-> d
  --         |     |
  --          -----
  --            ^
  --            |
  --            a
  -----------------------------------------------------------------------------
  *)

  Definition below {A B C D E F G}
              (r : A * B -> cava (D * G))
              (s : G * C -> cava (E * F))
              (abc : A * (B * C)) : cava ((D * E) * F) :=
    let '(a, (b, c)) := abc in
    '(d, g) <- r (a, b) ;;
    '(e, f) <- s (g, c) ;;
    ret ((d, e), f).

  (* The col combinator takes a 4-sided circuit element and replicates it by
    composing each element in a chain.

  -- COL r
  --            a
  --            ^
  --            |
  --          -----
  --         |     |
  --     b ->|  r  |-> c
  --         |     |
  --          -----
  --            ^
  --            |
  --            a
  --            ^
  --            |
  --          -----
  --         |     |
  --     b ->|  r  |-> c
  --         |     |
  --          -----
  --            ^
  --            |
  --            a
  --            ^
  --            |
  --          -----
  --         |     |
  --     b ->|  r  |-> c
  --         |     |
  --          -----
  --            ^
  --            |
  --            a
  -----------------------------------------------------------------------------

  *)

  Fixpoint col_generic {A B C}
             (circuit : A * B -> cava (C * A))
             (a : A) (b : list B)
    : cava (list C * A) :=
    match b with
    | [] => ret ([], a)
    | b0 :: b =>
      '(c0, a) <- circuit (a, b0) ;;
      '(c, a) <- col_generic circuit a b ;;
      ret (c0 :: c, a)
    end.

  Definition col {A B C}
             (circuit : A * B -> cava (signal C * A))
             (a : A) {n : nat} (b : Vector.t B n)
    : cava (signal (Vec C n) * A) :=
    '(c, a) <- col_generic circuit a (to_list b) ;;
    c <- packV (of_list_sized defaultSignal n c) ;;
    ret (c, a).

  (****************************************************************************)
  (* A binary tree combinator.                                                *)
  (****************************************************************************)

  (* n should be the maximum depth of the tree, inputs must not be empty *)
  Fixpoint tree_generic {T: Type}
           (circuit: T -> T -> cava T) (error: T)
           (n : nat) (inputs : list T) : cava T :=
    match n with
    | O =>
      (* for a depth of 0, only a singleton list is possible *)
      match inputs with
      | [t]%list => ret t
      | _ => ret error (* should not get here *)
      end
    | S n' =>
      if (1 <? length inputs)
      then
        (* if there are at least 2 elements, halve the input list *)
        let mid := (length inputs) / 2 in
        let iL := firstn mid inputs in
        let iR := skipn mid inputs in
        aS <- tree_generic circuit error n' iL ;;
        bS <- tree_generic circuit error n' iR ;;
        circuit aS bS
      else
        (* same as 0-depth case -- only a singleton list is possible *)
        match inputs with
        | [t]%list => ret t
        | _ => ret error (* should not get here *)
        end
    end.

  Definition tree {t : SignalType}
             (circuit: signal t * signal t -> cava (signal t))
             {n} (v : signal (Vec t n)) : cava (signal t) :=
    v <- unpackV v ;;
    tree_generic (fun a b => circuit (a,b))
                 defaultSignal (Nat.log2_up n) (to_list v).

 End WithCava.
