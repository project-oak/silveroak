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

Inductive NetExpr : signal -> Set :=
  | Net : Z -> NetExpr Bit
  | NetPair : forall {a b : signal},
              NetExpr a -> NetExpr b -> NetExpr (Tuple2 a b)
  | NoNet : NetExpr NoSignal.

Check Net 72 : NetExpr Bit.
Check NetPair (Net 22) (Net 8) : NetExpr (Tuple2 Bit Bit).
Check NetPair (NetPair (Net 22) (Net 8)) (Net 72) :
      NetExpr (Tuple2 (Tuple2 Bit Bit) Bit).

Inductive cava : signal -> signal -> Set :=
  | Input : string -> cava Bit Bit
  | Output : string -> cava Bit Bit
  | Inv : cava Bit Bit
  | And2 : cava (Tuple2 Bit Bit) Bit
  | Xor2 : cava (Tuple2 Bit Bit) Bit
  | Xorcy : cava (Tuple2 Bit Bit) Bit
  | Muxcy : cava (Tuple2 Bit (Tuple2 Bit Bit)) Bit
  | Delay : forall {A : signal}, cava A A
  | Compose : forall {A B C : signal}, cava A B -> cava B C -> cava A C
  | Par2 : forall {A B C D : signal}, cava A C -> cava B D ->
                                      cava (Tuple2 A B) (Tuple2 C D)
  | Rewire : forall {A B : signal}, (NetExpr A -> NetExpr B) -> cava A B.

Check Compose Inv Inv : cava Bit Bit.
Check Compose And2 Inv : cava (Tuple2 Bit Bit) Bit.
Check Compose Inv Delay : cava Bit Bit.

Notation " f ⟼ g " := (Compose f g)
  (at level 39, right associativity) : program_scope.

Notation " a ‖ b " := (Par2 a b)
  (at level 45, right associativity) : program_scope.

Definition fork2Fn {a:signal} (x:NetExpr a) : NetExpr (Tuple2 a a)
  := NetPair x x.

Definition swapFn {a:signal} {b:signal} (x:NetExpr (Tuple2 a b)) :
            NetExpr (Tuple2 b a)
  := match x with
     | NetPair p q => NetPair q p
     end.

Check swapFn (NetPair (Net 3) (Net 4)) : NetExpr (Tuple2 Bit Bit).

Definition fork2 := fun {t : signal} =>
                    Rewire (fun (x : NetExpr t) => NetPair x x).

Check Input "a" ⟼ Inv ⟼ fork2 ⟼ And2 : cava Bit Bit.

Definition id := fun {t : signal} =>
                Rewire (fun (x : NetExpr t) => x).

Definition first {A B X : signal} (a : cava A B) :
           cava (Tuple2 A X) (Tuple2 B X) := a ‖ id.

Definition second {A B X : signal} (a : cava A B) :
           cava (Tuple2 X A) (Tuple2 X B) := id ‖ a.           