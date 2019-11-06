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

Fixpoint signalDenote (s : signal) (T : Type) : Type := 
  match s with
  | Bit => T
  | NoSignal => unit
  | Tuple2 s1 s2 => signalDenote s1 T * signalDenote s2 T
  end.

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
  | Rewire : forall {A B : signal}, forall (f : forall t, signalDenote A t -> signalDenote B t), cava A B.


Definition inv : cava Bit Bit := Unaryop Inv.

Definition unaryopDenote (u : unaryop) (x : signalDenote Bit bool) : signalDenote Bit bool :=
  match u, x with
  | Inv, b => (negb b)
  end.

Definition and2 : cava ‹Bit, Bit› Bit  := Binop And2.
Definition xor2 : cava ‹Bit, Bit› Bit  := Binop Xor2.
Definition xorcy : cava ‹Bit, Bit› Bit := Binop Xorcy.

Definition and2_comb (xy : bool*bool) : bool := fst xy && snd xy.
Definition xor2_comb (xy : bool*bool) : bool := xorb (fst xy) (snd xy).

Definition binopDenote (b : binop) (xy : signalDenote ‹Bit, Bit› bool) : signalDenote Bit bool :=
  match xy with
   (xv, yv) => match b with
              | And2  => (xv && yv)
              | Xor2  => (xorb xv yv)
              | Xorcy => (xorb xv yv)
              end
         
  end.

Definition applyRewire {A B : signal} (f : forall {T:Type}, signalDenote A T -> signalDenote B T) (inp : signalDenote A bool) :
                       signalDenote B bool :=
  f inp.

Fixpoint cavaDenote {i o : signal} (e : cava i o) : (signalDenote i bool -> signalDenote o bool) :=
  match e with
  | Unaryop uop => unaryopDenote uop 
  | Binop bop => binopDenote bop
  | Muxcy => fun '(s, (a, b)) => if s then a else b 
  | Delay => fun a => a    
  | Compose f g => fun i => cavaDenote g (cavaDenote f i)
  | Par2 f g => 
      fun '(p, q) => ((cavaDenote f p), (cavaDenote g q))
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
  forall (a b : bool), cavaDenote nandGate (a, b) = negb (a && b).
auto.
Qed.

Definition swapFn {A B : signal} {T : Type} (x: signalDenote ‹A, B› T) : signalDenote ‹B, A› T
  := match x with
     | (p, q) => (q, p)
     end.


Check (@swapFn Bit Bit Z) (22%Z, 8%Z).
Check (@swapFn Bit Bit bool) (false, true).

Definition swap A B : cava ‹A, B› ‹B, A› := Rewire (@swapFn A B).

Definition fork2Fn {A:signal} {T:Type} (x: signalDenote A T) : signalDenote ‹A, A› T
  := (x, x).

Definition fork2 {A} : cava A ‹A, A› := Rewire (@fork2Fn A).

Check inv ⟼ fork2 ⟼ and2 : cava Bit Bit.

Definition idFn {A : signal} {T : Type} (x: signalDenote A T) : signalDenote A T := x.

Definition id {A} := Rewire (@idFn A).

Definition first {A B X : signal} (a : cava A B) :
           cava ‹A, X› ‹B, X› := a ‖ id.

Definition second {A B X : signal} (a : cava A B) :
           cava ‹X, A› ‹X, B›:= id ‖ a.

Definition forkBit {T : Type} (x : signalDenote Bit T) : signalDenote ‹Bit, Bit› T := (x, x).

Require Import Program.Equality.


Definition swapBit (T : Type) (inp : signalDenote ‹Bit, Bit› T) : signalDenote ‹Bit, Bit› T := 
  match inp with (x, y) => (y, x)
  end.



Definition tupleLeft {A B C : signal} {T : Type} (x : @signalDenote ‹A, ‹B, C›› T) :
                                                  signalDenote ‹‹A, B›, C› T
   := match x with (p, (q, r)) => ((p, q), r) end.

(*

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
*)           