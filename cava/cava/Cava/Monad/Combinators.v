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

From Coq Require Import Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.MonadFix.
From Coq Require Arith.PeanoNat.
Require Import Omega.

Export MonadNotation.

Require Import Cava.Monad.Cava.

Generalizable All Variables.

Local Open Scope monad_scope.


(******************************************************************************)
(* Lava-style circuit combinators.                                            *)
(******************************************************************************)


(* Below combinator

-------------------------------------------------------------------------------
-- Below
-------------------------------------------------------------------------------
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
-------------------------------------------------------------------------------
*)

Fixpoint below `{Monad m} {A B C D E F G}
             (r : A * B -> m (D * G)%type)
             (s : G * C -> m (E * F)%type)
             (abc : A * (B * C)) : m ((D * E) * F)%type :=
  let (a, bc) := abc in
  let (b, c) := bc in
  dg <- r (a, b) ;;
  let (d, g) := dg : D * G in
  ef <- s (g, c) ;;
  let (e, f) := ef : E * F in
  ret ((d, e), f).

(* The col combinator takes a 4-sided circuit element and replicates it by
   composing each element in a chain.

-------------------------------------------------------------------------------
-- 4-Sided Tile Combinators 
-------------------------------------------------------------------------------
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
-------------------------------------------------------------------------------


*)

Fixpoint col' `{Monad m} {A B C}
              (circuit : A * B -> m (C * A)%type) (a : A) (b : list B) :
              m (list C * A)%type :=
  match b with
  | [] => ret ([], a)
  | b0::br => c_cs_e <- below circuit (fun ab => col' circuit (fst ab) (snd ab)) (a, (b0, br)) ;;
              let (c_cs, e) := c_cs_e : (C * list C) * A in
              let (c, cs) := c_cs : C * list C in
              ret (c::cs, e)
  end.

Definition col `{Monad m} {A B C}
                (circuit : A * B -> m (C * A)%type) (ab : A * list B) :
                m (list C * A)%type :=
  col' circuit (fst ab) (snd ab).

Definition fork2 `{Mondad_m : Monad m} {A} (a:A) := ret (a, a).

Definition first `{Mondad_m : Monad m} {A B C} (f : A -> m C) (ab : A * B) : m (C * B)%type :=
  let '(a, b) := ab in
  c <- f a ;;
  ret (c, b).

Definition second `{Mondad_m : Monad m} {A B C} (f : B -> m C) (ab : A * B) : m (A * C)%type :=
  let '(a, b) := ab in
  c <- f b ;;
  ret (a, c).

(******************************************************************************)
(* Split a bus into two halves.                                               *)
(******************************************************************************)

Definition halve {A} (l : list A) : list A * list A :=
  let mid := (length l) / 2 in
  (firstn mid l, skipn mid l).

(******************************************************************************)
(* A binary tree combinator.                                                  *)
(******************************************************************************)

Fixpoint tree {m bit} `{Cava m bit} circuit
              (n : nat) (v: list (list bit)) : m (list bit) :=
  match n with
  | O => match v with
         | [a; b] => circuit a b
         | _ => ret [] (* Error case *)
         end
  | S n' => let '(vL, vH) := halve v in
            aS <- tree circuit n' vL ;;
            bS <- tree circuit n' vH ;;
            sum <- circuit aS bS ;;
            ret sum
  end.

(******************************************************************************)
(* Loop combinator                                                            *)
(******************************************************************************)

(*

   ------------
  |    ----    |
  |-->|    |---  C (looped back)
      |    |
  A ->|    | -> B
       ----

It seems like I need a recursive-do style definition here to allow me to
use c in the result and as an argument to circuit.

loop :: MonadFix m => ((a, c) -> m (b, c)) -> a -> m b
loop circuit a
  = mdo (b, c) <- circuit (a, c)
        return b

or explicitly in terms of mfix:

loopMF' :: MonadFix m => ((a, c) -> m (b, c)) -> a -> m (b, c)
loopMF' circuit a
  = mfix (\bc -> do (b, c') <- circuit (a, snd bc)
                    return (b, c'))

loopMF :: MonadFix m => ((a, c) -> m (b, c)) -> a -> m b
loopMF circuit a
  = do (b, _) <- loopMF' circuit a 
       return b

Now... how to do the same thing in Coq?

loopS does causes Coq to go into an infinite looop.

Definition loopS 
           (circuit : (Z * Z) -> state CavaState Z) (a:Z) : state CavaState Z :=
  '(b, _) <- mfix (fun f bc => '(b, c') <- circuit (a, snd bc) ;;
                               ret (b, c')
                  ) (a, 0) ;;
  ret b.



Definition loop `{Monad m} `{MonadFix m} {A B}
           (circuit : (A * nat)%type -> m (B * nat)%type) (a:A) : m B :=
  '(b, _) <- mfix (fun f bc => '(b, c') <- circuit (a, snd bc) ;;
                               ret (b, c')
                  ) (a, 0) ;;
  ret b.

Definition nand2 `{Cava m bit} (ab : bit * bit) : m bit :=
  (and_gate >=> not_gate) [fst ab; snd ab].

(* loopedNAND also causes Coq to go into an infinite loop. *)

Set Typeclasses Debug.

Definition loopedNAND {Cava m bit} `{MonadFix m} (ab : list bit) : m bit := 
  loop (nand2 >=> delayBit >=> fork2) ab.

*)

