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
Notation "‹ x , y ›" := (Tuple2 x y).


Inductive Expr {T:Type} : signal -> Type :=
  | Net : T -> Expr Bit
  | NetPair : forall {a b : signal},
              Expr a -> Expr b -> Expr (Tuple2 a b)
  | NoNet : Expr NoSignal.


Check Net 42%Z : @Expr Z Bit.
Check NetPair (Net 22%Z) (Net 8%Z) : Expr ‹Bit, Bit›.
Check NetPair (NetPair (Net 22%Z) (Net 8%Z)) (Net 42%Z) :  Expr ‹‹Bit, Bit›, Bit›.


Inductive unaryop : Set :=
  | Inv.

Inductive binop : Set :=
  | And2
  | Xor2
  | Xorcy.

Inductive cava : signal -> signal -> Type :=
  | Unaryop : unaryop -> cava Bit Bit
  | Binop : binop -> cava ‹Bit, Bit› Bit
  | Muxcy : cava ‹Bit, ‹Bit, Bit›› Bit
  | Delay : forall {A : signal}, cava A A
  | Compose : forall {A B C : signal}, cava A B -> cava B C -> cava A C
  | Par2 : forall {A B C D : signal}, cava A C -> cava B D ->
                                      cava ‹A, B› ‹C, D›
  | Rewire : forall {A B : signal}, (forall {T:Type}, @Expr T A -> @Expr T B) -> cava A B.

Definition inv : cava Bit Bit := Unaryop Inv.

Definition unaryopDenote (u : unaryop) (x : Expr Bit) : Expr Bit :=
  match u, x with
  | Inv, Net xv => Net (negb xv)
  end.

Definition and2 : cava ‹Bit, Bit› Bit  := Binop And2.
Definition xor2 : cava ‹Bit, Bit› Bit  := Binop Xor2.
Definition xorcy : cava ‹Bit, Bit› Bit := Binop Xorcy.

Definition and2_comb (xy : bool*bool) : bool := fst xy && snd xy.
Definition xor2_comb (xy : bool*bool) : bool := xorb (fst xy) (snd xy).

Definition binopDenote (b : binop) (xy : Expr ‹Bit, Bit›) : Expr Bit :=
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
Check Compose and2 inv : cava ‹Bit, Bit› Bit.
(* Check Compose inv Delay : cava Bit Bit. *)

Notation " f ⟼ g " := (Compose f g)
  (at level 39, right associativity) : program_scope.

Notation " a ‖ b " := (Par2 a b)
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


Definition swapFn {A:signal} {B:signal} {T:Type} (x: @Expr T ‹A, B›) : @Expr T ‹B, A›
  := match x with
     | NetPair p q => NetPair q p
     end.

Check swapFn (NetPair (Net 22%Z) (Net 8%Z))   : @Expr Z    ‹Bit, Bit›.
Check swapFn (NetPair (Net false) (Net true)) : @Expr bool ‹Bit, Bit›.


Definition swap A B : cava ‹A, B› ‹B, A› := Rewire (@swapFn A B).

Definition fork2Fn {A:signal} {T:Type} (x:@Expr T A) : @Expr T ‹A, A›
  := NetPair x x.

Definition fork2 {A} : cava A ‹A, A› := Rewire (@fork2Fn A).

Check inv ⟼ fork2 ⟼ and2 : cava Bit Bit.

Definition idFn {A : signal} {T : Type} (x: @Expr T A) : @Expr T A
  := x.

Definition id {A} := Rewire (@idFn A).

Definition first {A B X : signal} (a : cava A B) :
           cava ‹A, X› ‹B, X› := a ‖ id.

Definition second {A B X : signal} (a : cava A B) :
           cava ‹X, A› ‹X, B›:= id ‖ a.

Definition forkBit {T : Type} (x : @Expr T  Bit) : @Expr T ‹Bit, Bit›
  := match x with
     | Net n => NetPair (Net n) (Net n)
     end.

(*
Definition swapBit {T : Type} (inp : @Expr T ‹Bit, Bit›) : @Expr T ‹Bit, Bit›
  := match inp in Expr ‹Bit, Bit› return Expr ‹Bit, Bit› with
     | NetPair x y => NetPair y x
     end.
*)

Definition tupleLeft {A B C : signal} {T : Type} (x : @Expr T ‹A, ‹B, C››) :
                                                  @Expr T ‹‹A, B›, C›
   := match x with
      | NetPair p qr => match qr with
                          NetPair q r => NetPair (NetPair p q) r
                        end
      end.

Definition belowReorg1 {a b e : signal} {T : Type}
                       (abe : @Expr T ‹a, ‹b, e››) : @Expr T  ‹‹a, b›, e›
  := match abe with
       NetPair a be => match be with
                         NetPair b e => NetPair (NetPair a b) e
                       end
     end.


Definition belowReorg2 {c d e : signal} {T : Type}
                       (cde : @Expr T ‹‹c, d›, e›) : @Expr T  ‹c, ‹d, e››
  := match cde with
       NetPair cd e => match cd with
                         NetPair c d => NetPair c (NetPair d e)
                       end
     end.

Definition belowReorg3 {c f g : signal} {T : Type}
                       (cfg : @Expr T ‹c, ‹f, g››) : @Expr T  ‹‹c, f›, g›
  := match cfg with
       NetPair c fg => match fg with
                         NetPair f g => NetPair (NetPair c f) g
                       end
     end.

Definition below {A B C D E F G : signal} {T : Type}
                 (f : cava  ‹A, B› ‹C, D›) (g: cava ‹D, E› ‹F, G›) 
                 (input : @Expr T ‹A,  ‹B, E››) :
                 cava  ‹A,  ‹B, E››  ‹‹C, F›, G›
  := Rewire (@belowReorg1 A B E) ⟼ first f ⟼ Rewire (@belowReorg2 C D E) ⟼ second g ⟼ Rewire (@belowReorg3 C F G).
           