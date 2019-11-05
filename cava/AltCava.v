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

Inductive signal : Type :=
  | Bit : signal
  | NoSignal
  | Tuple2 : signal -> signal -> signal.
Notation "\u2039 x , y \u203a" := (Tuple2 x y).


Inductive Expr {T:Type} : signal -> Type :=
  | Net : T -> Expr Bit
  | NetPair : forall {a b : signal},
              Expr a -> Expr b -> Expr (Tuple2 a b)
  | NoNet : Expr NoSignal.


Check Net 42%Z : @Expr Z Bit.
Check NetPair (Net 22%Z) (Net 8%Z) : Expr \u2039Bit, Bit\u203a.
Check NetPair (NetPair (Net 22%Z) (Net 8%Z)) (Net 42%Z) :  Expr \u2039\u2039Bit, Bit\u203a, Bit\u203a.


Inductive unaryop : Set :=
  | Inv.

Inductive binop : Set :=
  | And2
  | Xor2
  | Xorcy.

Inductive cava : signal -> signal -> Type :=
  | Unaryop : unaryop -> cava Bit Bit
  | Binop : binop -> cava \u2039Bit, Bit\u203a Bit
  | Muxcy : cava \u2039Bit, \u2039Bit, Bit\u203a\u203a Bit
  | Delay : forall {A : signal}, cava A A
  | Compose : forall {A B C : signal}, cava A B -> cava B C -> cava A C
  | Par2 : forall {A B C D : signal}, cava A C -> cava B D ->
                                      cava \u2039A, B\u203a \u2039C, D\u203a
  | Rewire : forall {A B : signal}, (forall {T:Type}, @Expr T A -> @Expr T B) -> cava A B.

Definition inv : cava Bit Bit := Unaryop Inv.

Definition unaryopDenote (u : unaryop) (x : Expr Bit) : Expr Bit :=
  match u, x with
  | Inv, Net xv => Net (negb xv)
  end.

Definition and2 : cava \u2039Bit, Bit\u203a Bit  := Binop And2.
Definition xor2 : cava \u2039Bit, Bit\u203a Bit  := Binop Xor2.
Definition xorcy : cava \u2039Bit, Bit\u203a Bit := Binop Xorcy.

Definition and2_comb (xy : bool*bool) : bool := fst xy && snd xy.
Definition xor2_comb (xy : bool*bool) : bool := xorb (fst xy) (snd xy).

Definition binopDenote (b : binop) (xy : Expr \u2039Bit, Bit\u203a) : Expr Bit :=
  match xy in Expr (Tuple2 Bit Bit) return Expr Bit with
    NetPair xb yb
      => match xb, yb with
           Net xv, Net yv
           => match b with
              | And2  => Net (xv && yv)
              | Xor2  => Net (xorb xv yv)
              | Xorcy => Net (xorb xv yv)
              end
         end
  end.


Definition swapFn {A:signal} {B:signal} {T:Type} (x: @Expr T \u2039A, B\u203a) : @Expr T \u2039B, A\u203a
  := match x with
     | NetPair p q => NetPair q p
     end.

Check swapFn (NetPair (Net 22%Z) (Net 8%Z))   : @Expr Z    \u2039Bit, Bit\u203a.
Check swapFn (NetPair (Net false) (Net true)) : @Expr bool \u2039Bit, Bit\u203a.


Definition swap A B : cava \u2039A, B\u203a \u2039B, A\u203a := Rewire (@swapFn A B).


Definition applyRewire {A B : signal} (f : forall {T:Type}, @Expr T A -> @Expr T B) (inp : @Expr bool A) :
                       @Expr bool B :=
  f inp.

Fixpoint cavaDenote {i o : signal} (e : cava i o) :=
  match e with
  | Unaryop uop => unaryopDenote uop
  | Binop bop => binopDenote bop
  | Muxcy => fun {sab : Expr (Tuple2 Bit (Tuple2 Bit Bit))} =>
               match sab with
                 NetPair sB abB =>
                   match sB with
                     Net s =>
                       match abB with
                         NetPair aB bB =>
                           match aB, bB with
                             Net a, Net b => Net (if s then a else b)
                           end
                       end
                   end
               end
  | Delay => fun a => a    
  | Compose f g => fun i => cavaDenote g (cavaDenote f i)
  | Par2 f g =>
      fun inp =>
        (match inp with
           NetPair p q =>
           fun w r => NetPair (w p) (r q)
         end) (cavaDenote f) (cavaDenote g)
  | Rewire f => applyRewire f
  end.

Inductive cavaTop : signal -> signal -> Type :=
  | Input : string -> cavaTop Bit Bit
  | Output : string -> cavaTop Bit Bit
  | Circuit : forall {A B : signal}, cavaTop A B.

Check Compose inv inv : cava Bit Bit.
Check Compose and2 inv : cava \u2039Bit, Bit\u203a Bit.
(* Check Compose inv Delay : cava Bit Bit. *)

Notation " f ⟼ g " := (Compose f g)
  (at level 39, right associativity) : program_scope.

Notation " a ‖ " := (Par2 a b)
  (at level 45, right associativity) : program_scope.

Definition nandGate := and2 ⟼ inv.

Lemma nandGate_proof :
  forall (a b : bool), cavaDenote nandGate (NetPair (Net a) (Net b)) = Net (negb (a && b)).
Proof.
  intros a b.
  unfold cavaDenote.
  simpl.
  reflexivity.
Qed.

Definition fork2Fn {a:signal} (x:NetExpr a) : NetExpr \u2039a, a\u203a
  := NetPair x x.

Definition swapFn {a:signal} {b:signal} (x:NetExpr \u2039a, b\u203a) :
            NetExpr \u2039b, a\u203a
  := match x with
     | NetPair p q => NetPair q p
     end.

Check swapFn (NetPair (Net 3) (Net 4)) : NetExpr \u2039Bit, Bit\u203a.

Definition fork2 := fun {t : signal} =>
                    Rewire (fun (x : NetExpr t) => NetPair x x).

Check Input "a" ⟼ Inv ⟼ fork2 ⟼ And2 : cava Bit Bit.

Definition id := fun {t : signal} =>
                Rewire (fun (x : NetExpr t) => x).

Definition first {A B X : signal} (a : cava A B) :
           cava \u2039A, X\u203a \u2039B, X\u203a := a \u2016 id.

Definition second {A B X : signal} (a : cava A B) :
           cava \u2039X, A\u203a \u2039X, B\u203a:= id \u2016 a.

Definition forkBit (x : NetExpr Bit) : NetExpr \u2039Bit, Bit\u203a
  := match x with
     | Net n => NetPair (Net n) (Net n)
     end.

Definition swapBit (x : NetExpr \u2039Bit, Bit\u203a) : NetExpr \u2039Bit, Bit\u203a
  := match x with
     | @NetPair Bit Bit x y => NetPair y x
     end.

Definition tupleLeft {a b c : signal} (x:NetExpr \u2039a, \u2039b, c\u203a\u203a) :
                                      NetExpr \u2039\u2039a, b\u203a, c\u203a
   := match x with
      | NetPair p qr => match qr with
                          NetPair q r => NetPair (NetPair p q) r
                        end
      end.

Definition belowReorg1 {a b e : signal}
                       (abe : NetExpr \u2039a, \u2039b, e\u203a\u203a) : NetExpr  \u2039\u2039a, b\u203a, e\u203a
  := match abe with
       NetPair a be => match be with
                         NetPair b e => NetPair (NetPair a b) e
                       end
     end.


Definition belowReorg2 {c d e : signal}
                       (cde : NetExpr \u2039\u2039c, d\u203a, e\u203a) : NetExpr  \u2039c, \u2039d, e\u203a\u203a
  := match cde with
       NetPair cd e => match cd with
                         NetPair c d => NetPair c (NetPair d e)
                       end
     end.

Definition belowReorg3 {c f g : signal}
                       (cfg : NetExpr \u2039c, \u2039f, g\u203a\u203a) : NetExpr  \u2039\u2039c, f\u203a, g\u203a
  := match cfg with
       NetPair c fg => match fg with
                         NetPair f g => NetPair (NetPair c f) g
                       end
     end.

Definition below {A B C D E F G : signal} (f : cava  \u2039A, B\u203a \u2039C, D\u203a) (g: cava \u2039D, E\u203a \u2039F, G\u203a) 
                                          (input : NetExpr \u2039A,  \u2039B, E\u203a\u203a) :
                                          cava  \u2039A,  \u2039B, E\u203a\u203a  \u2039\u2039C, F\u203a, G\u203a
  := Rewire belowReorg1 ⟼ first f ⟼ Rewire belowReorg2 ⟼ second g ⟼ Rewire belowReorg3.
           