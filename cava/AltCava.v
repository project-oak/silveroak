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

Notation "\u27e8 x , y \u3009" := (Tuple2 x y).

Inductive NetExpr : signal -> Set :=
  | Net : Z -> NetExpr Bit
  | NetPair : forall {a b : signal},
              NetExpr a -> NetExpr b -> NetExpr (Tuple2 a b)
  | NoNet : NetExpr NoSignal.

Check Net 72 : NetExpr Bit.
Check NetPair (Net 22) (Net 8) : NetExpr \u27e8Bit, Bit\u3009.
Check NetPair (NetPair (Net 22) (Net 8)) (Net 72) :
      NetExpr \u27e8\u27e8Bit, Bit\u3009, Bit\u3009.

Inductive cava : signal -> signal -> Set :=
  | Input : string -> cava Bit Bit
  | Output : string -> cava Bit Bit
  | Inv : cava Bit Bit
  | And2 : cava \u27e8Bit, Bit\u3009 Bit
  | Xor2 : cava \u27e8Bit, Bit\u3009 Bit
  | Xorcy : cava \u27e8Bit, Bit\u3009 Bit
  | Muxcy : cava \u27e8Bit, \u27e8Bit, Bit\u3009\u3009 Bit
  | Delay : forall {A : signal}, cava A A
  | Compose : forall {A B C : signal}, cava A B -> cava B C -> cava A C
  | Par2 : forall {A B C D : signal}, cava A C -> cava B D ->
                                      cava \u27e8A, B\u3009 \u27e8C, D\u3009
  | Rewire : forall {A B : signal}, (NetExpr A -> NetExpr B) -> cava A B.

Check Compose Inv Inv : cava Bit Bit.
Check Compose And2 Inv : cava \u27e8Bit, Bit\u3009 Bit.
Check Compose Inv Delay : cava Bit Bit.

Notation " f \u27fc g " := (Compose f g)
  (at level 39, right associativity) : program_scope.

Notation " a \u2016 b " := (Par2 a b)
  (at level 45, right associativity) : program_scope.

Definition fork2Fn {a:signal} (x:NetExpr a) : NetExpr \u27e8a, a\u3009
  := NetPair x x.

Definition swapFn {a:signal} {b:signal} (x:NetExpr \u27e8a, b\u3009) :
            NetExpr \u27e8b, a\u3009
  := match x with
     | NetPair p q => NetPair q p
     end.

Check swapFn (NetPair (Net 3) (Net 4)) : NetExpr \u27e8Bit, Bit\u3009.

Definition fork2 := fun {t : signal} =>
                    Rewire (fun (x : NetExpr t) => NetPair x x).

Check Input "a" \u27fc Inv \u27fc fork2 \u27fc And2 : cava Bit Bit.

Definition id := fun {t : signal} =>
                Rewire (fun (x : NetExpr t) => x).

Definition first {A B X : signal} (a : cava A B) :
           cava \u27e8A, X\u3009 \u27e8B, X\u3009 := a \u2016 id.

Definition second {A B X : signal} (a : cava A B) :
           cava \u27e8X, A\u3009 \u27e8X, B\u3009:= id \u2016 a.

Definition forkBit (x : NetExpr Bit) : NetExpr \u27e8Bit, Bit\u3009
  := match x with
     | Net n => NetPair (Net n) (Net n)
     end.

Definition swapBit (x : NetExpr \u27e8Bit, Bit\u3009) : NetExpr \u27e8Bit, Bit\u3009
  := match x with
     | @NetPair Bit Bit x y => NetPair y x
     end.

Definition tupleLeft {a b c : signal} (x:NetExpr \u27e8a, \u27e8b, c\u3009\u3009) :
                                      NetExpr \u27e8\u27e8a, b\u3009, c\u3009
   := match x with
      | NetPair p qr => match qr with
                          NetPair q r => NetPair (NetPair p q) r
                        end
      end.

Definition belowReorg1 {a b e : signal}
                       (abe : NetExpr \u27e8a, \u27e8b, e\u3009\u3009) : NetExpr  \u27e8\u27e8a, b\u3009, e\u3009
  := match abe with
       NetPair a be => match be with
                         NetPair b e => NetPair (NetPair a b) e
                       end
     end.


Definition belowReorg2 {c d e : signal}
                       (cde : NetExpr \u27e8\u27e8c, d\u3009, e\u3009) : NetExpr  \u27e8c, \u27e8d, e\u3009\u3009
  := match cde with
       NetPair cd e => match cd with
                         NetPair c d => NetPair c (NetPair d e)
                       end
     end.

Definition belowReorg3 {c f g : signal}
                       (cfg : NetExpr \u27e8c, \u27e8f, g\u3009\u3009) : NetExpr  \u27e8\u27e8c, f\u3009, g\u3009
  := match cfg with
       NetPair c fg => match fg with
                         NetPair f g => NetPair (NetPair c f) g
                       end
     end.

Definition below {A B C D E F G : signal} (f : cava  \u27e8A, B\u3009 \u27e8C, D\u3009) (g: cava \u27e8D, E\u3009 \u27e8F, G\u3009) 
                                          (input : NetExpr \u27e8A,  \u27e8B, E\u3009\u3009) :
                                          cava  \u27e8A,  \u27e8B, E\u3009\u3009  \u27e8\u27e8C, F\u3009, G\u3009
  := Rewire belowReorg1 \u27fc first f \u27fc Rewire belowReorg2 \u27fc second g \u27fc Rewire belowReorg3.
           