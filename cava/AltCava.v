(****************************************************************************)
(* Copyright 2019 The Project Oak Authors                                   *)
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

From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
From Coq Require Import ZArith.
From Coq Require Import extraction.ExtrHaskellZInteger.
Require Import Program.Basics.
Local Open Scope program_scope.

Inductive signal : Set :=
  | Bit : signal
  | NoSignal
  | Tuple2 : signal -> signal -> signal.

Notation "‹ x , y ›" := (Tuple2 x y).

Inductive NetExpr : signal -> Set :=
  | Net : Z -> NetExpr Bit
  | NetPair : forall {a b : signal},
              NetExpr a -> NetExpr b -> NetExpr (Tuple2 a b)
  | NoNet : NetExpr NoSignal.

Check Net 72 : NetExpr Bit.
Check NetPair (Net 22) (Net 8) : NetExpr ‹Bit, Bit›.
Check NetPair (NetPair (Net 22) (Net 8)) (Net 72) :
      NetExpr ‹‹Bit, Bit›, Bit›.

Inductive cava : signal -> signal -> Set :=
  | Input : string -> cava Bit Bit
  | Output : string -> cava Bit Bit
  | Inv : cava Bit Bit
  | And2 : cava ‹Bit, Bit› Bit
  | Xor2 : cava ‹Bit, Bit› Bit
  | Xorcy : cava ‹Bit, Bit› Bit
  | Muxcy : cava ‹Bit, ‹Bit, Bit›› Bit
  | Delay : forall {A : signal}, cava A A
  | Compose : forall {A B C : signal}, cava A B -> cava B C -> cava A C
  | Par2 : forall {A B C D : signal}, cava A C -> cava B D ->
                                      cava ‹A, B› ‹C, D›
  | Rewire : forall {A B : signal}, (NetExpr A -> NetExpr B) -> cava A B.

Check Compose Inv Inv : cava Bit Bit.
Check Compose And2 Inv : cava ‹Bit, Bit› Bit.
Check Compose Inv Delay : cava Bit Bit.

Notation " f ⟼ g " := (Compose f g)
  (at level 39, right associativity) : program_scope.

Notation " a ‖ b " := (Par2 a b)
  (at level 45, right associativity) : program_scope.

Definition fork2Fn {a:signal} (x:NetExpr a) : NetExpr ‹a, a›
  := NetPair x x.

Definition swapFn {a:signal} {b:signal} (x:NetExpr ‹a, b›) :
            NetExpr ‹b, a›
  := match x with
     | NetPair p q => NetPair q p
     end.

Check swapFn (NetPair (Net 3) (Net 4)) : NetExpr ‹Bit, Bit›.

Definition fork2 := fun {t : signal} =>
                    Rewire (fun (x : NetExpr t) => NetPair x x).

Check Input "a" ⟼ Inv ⟼ fork2 ⟼ And2 : cava Bit Bit.

Definition id := fun {t : signal} =>
                Rewire (fun (x : NetExpr t) => x).

Definition first {A B X : signal} (a : cava A B) :
           cava ‹A, X› ‹B, X› := a ‖ id.

Definition second {A B X : signal} (a : cava A B) :
           cava ‹X, A› ‹X, B›:= id ‖ a.

Definition forkBit (x : NetExpr Bit) : NetExpr ‹Bit, Bit›
  := match x with
     | Net n => NetPair (Net n) (Net n)
     end.

Definition swapBit (x : NetExpr ‹Bit, Bit›) : NetExpr ‹Bit, Bit›
  := match x with
     | @NetPair Bit Bit x y => NetPair y x
     end.

Definition tupleLeft {a b c : signal} (x:NetExpr ‹a, ‹b, c››) :
                                      NetExpr ‹‹a, b›, c›
   := match x with
      | NetPair p qr => match qr with
                          NetPair q r => NetPair (NetPair p q) r
                        end
      end.

Definition belowReorg1 {a b e : signal}
                       (abe : NetExpr ‹a, ‹b, e››) : NetExpr  ‹‹a, b›, e›
  := match abe with
       NetPair a be => match be with
                         NetPair b e => NetPair (NetPair a b) e
                       end
     end.


Definition belowReorg2 {c d e : signal}
                       (cde : NetExpr ‹‹c, d›, e›) : NetExpr  ‹c, ‹d, e››
  := match cde with
       NetPair cd e => match cd with
                         NetPair c d => NetPair c (NetPair d e)
                       end
     end.

Definition belowReorg3 {c f g : signal}
                       (cfg : NetExpr ‹c, ‹f, g››) : NetExpr  ‹‹c, f›, g›
  := match cfg with
       NetPair c fg => match fg with
                         NetPair f g => NetPair (NetPair c f) g
                       end
     end.

Definition below {A B C D E F G : signal} (f : cava  ‹A, B› ‹C, D›) (g: cava ‹D, E› ‹F, G›) 
                                          (input : NetExpr ‹A,  ‹B, E››) :
                                          cava  ‹A,  ‹B, E››  ‹‹C, F›, G›
  := Rewire belowReorg1 ⟼ first f ⟼ Rewire belowReorg2 ⟼ second g ⟼ Rewire belowReorg3.
           