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

(* shape describes the shape of the wires coming into our out of a circuit
   block.
*)
Inductive shape : Type :=
  | Bit : shape                        (* A single wire *)
  | Tuple2 : shape -> shape -> shape.  (* A pair of bundles of wires *)
Notation "‹ x , y ›" := (Tuple2 x y).


(* A signal represents the values that 'flow' along wires. Different types
   for the wire values correspond to different interpretations of circuit
   descriptions. T set to bool is used for combinational logic semantics,
   T set to list bool is used for sequential circuit semantics, and
   T set to Z is used for generating circuit netlists for VHDL generation.
*)
Fixpoint signal {T : Type} (s : shape) : Type := 
  match s with
  | Bit => T
  | ‹s1, s2› => @signal T s1 * @signal T s2
  end.


Definition boolSignal := @signal bool.
Definition intSignal := @signal Z.
Definition boolPair := @signal bool ‹Bit, Bit› .
Definition intPair := @signal Z ‹Bit, Bit› .

(* Primitive unary circuit elements. *)
Inductive unaryop : Set :=
  | Inv.

(* Primitive binary circuit elements. *)
Inductive binop : Set :=
  | And2
  | Xor2
  | Xorcy. (* Xorcy is an XOR in the fast carry chain on Xilinx FPGAs *)

(* The type cava describes a circuit block where the first parameter describes
   the shape of the circuit input and the second parameter describes the shape
   of the circuit output.
*)
Inductive cava : shape -> shape -> Type :=
  | Unaryop : unaryop -> cava Bit Bit
  | Binop : binop -> cava ‹Bit, Bit› Bit
  | Muxcy : cava ‹Bit, ‹Bit, Bit›› Bit  (* (s, (di, ci)) output is di if s false, ci otherwise *)
  | Delay : forall {A : shape}, cava A A
  | Compose : forall {A B C : shape}, cava A B -> cava B C -> cava A C
  | Par2 : forall {A B C D : shape}, cava A C -> cava B D ->
                                     cava ‹A, B› ‹C, D›
  | Reshape : forall {A B : shape}, forall (f : forall T, @signal T A -> @signal T B), cava A B
  | Input : forall {A : shape}, string -> cava A A
  | Output : forall {A : shape}, string -> cava A A.

(* An invertor circuit description, and its combinational logic semantics. *)
Definition inv : cava Bit Bit := Unaryop Inv.

Definition unaryopDenote (u : unaryop) (x : signal Bit) : signal Bit :=
  match u, x with
  | Inv, b => negb b
  end.

(* Some binary input circuit blocks, and their combinational logic semantics. *)
Definition and2 : cava ‹Bit, Bit› Bit  := Binop And2.
Definition xor2 : cava ‹Bit, Bit› Bit  := Binop Xor2.
Definition xorcy : cava ‹Bit, Bit› Bit := Binop Xorcy.

Definition binopDenote (b : binop) (xy : signal ‹Bit, Bit›) : signal Bit :=
  match xy with
    (x, y) => match b with
              | And2  => x && y
              | Xor2  => xorb x y
              | Xorcy => xorb x y
              end
  end.

Definition and2_comb (xy : bool*bool) : bool := fst xy && snd xy.
Definition xor2_comb (xy : bool*bool) : bool := xorb (fst xy) (snd xy).

(* applyReshape allows us apply a generic reshaping function to the input to
   produce a reshaped output to give a semantic interpretation for combinational
   circuits.
*)
Definition applyReshape {A B : shape} (f : forall {T:Type}, @signal T A -> @signal T B) (inp : @signal bool A) :
                        @signal bool B :=
  f inp.

(* A semantics for combinational circuits. For now consider delay to just be an identity function. *)
Fixpoint cavaCombinational {i o : shape} (e : cava i o) : (@signal bool i -> @signal bool o) :=
  match e with
  | Unaryop uop => unaryopDenote uop 
  | Binop bop => binopDenote bop
  | Muxcy => fun '(s, (di, ci)) => if s then ci else di 
  | Delay => fun a => a    
  | Compose f g => fun i => cavaCombinational g (cavaCombinational f i)
  | Par2 f g => 
      fun '(p, q) => (cavaCombinational f p, cavaCombinational g q)
  | Reshape f => applyReshape f
  | Input _ => fun x => x
  | Output _ => fun x => x
  end.

Check Compose inv inv : cava Bit Bit.
Check Compose and2 inv : cava ‹Bit, Bit› Bit.
Check Compose inv Delay : cava Bit Bit.

Notation " f ⟼ g " := (Compose f g)
  (at level 39, right associativity) : program_scope.

Notation " a ‖ b " := (Par2 a b)
  (at level 45, right associativity) : program_scope.

Definition swapFn {A B : shape} {T : Type} (x: @signal T ‹A, B›) : @signal T ‹B, A›
  := match x with (p, q) => (q, p) end.

Check (@swapFn Bit Bit Z) (22%Z, 8%Z).
Check (@swapFn Bit Bit bool) (false, true).

Definition swap A B : cava ‹A, B› ‹B, A› := Reshape (@swapFn A B).

Definition fork2Fn {A :shape} {T : Type} (x: @signal T A) : @signal T ‹A, A›
  := (x, x).

Definition fork2 {A : shape} : cava A ‹A, A› := Reshape (@fork2Fn A).

Check inv ⟼ fork2 ⟼ and2 : cava Bit Bit.

Definition idFn {A : shape} {T : Type} (x: @signal T A) : @signal T A := x.

Definition id {A} := Reshape (@idFn A).

Definition first {A B X : shape} (a : cava A B) :
           cava ‹A, X› ‹B, X› := a ‖ id.

Definition second {A B X : shape} (a : cava A B) :
           cava ‹X, A› ‹X, B›:= id ‖ a.

Definition forkBit {T : Type} (x : @signal T Bit) : @signal T ‹Bit, Bit› := (x, x).


(* A version of swap specialized to a tuple of bits. *)
Definition swapBitFn (T : Type) (inp : @signal T ‹Bit, Bit›) : @signal T ‹Bit, Bit› := 
  match inp with (x, y) => (y, x)
end.

Definition swapBit := Reshape swapBitFn.

Definition tupleLeftFn {A B C : shape} {T : Type} (x : @signal T ‹A, ‹B, C››) :
                                                   @signal T ‹‹A, B›, C›
   := match x with (p, (q, r)) => ((p, q), r)
      end.

Definition tupleLeft {A B C : shape} := Reshape (@tupleLeftFn A B C).

Definition belowReorg1 {A B E : shape} {T : Type}
                       (abe : @signal T ‹A, ‹B, E››) : @signal T  ‹‹A, B›, E›
  := match abe with
       (a, (b, e)) =>  ((a, b), e)
     end.

Definition belowReorg2 {C D E : shape} {T : Type}
                       (cde : @signal T ‹‹C, D›, E›) : @signal T  ‹C, ‹D, E››
  := match cde with
       ((c, d), e) => (c, (d, e))
     end.

Definition belowReorg3 {C F G : shape} {T : Type}
                       (cfg : @signal T ‹C, ‹F, G››) : @signal T  ‹‹C, F›, G›
  := match cfg with
       (c, (f, g)) => ((c, f), g)
     end.

Definition below {A B C D E F G : shape} {T : Type}
                 (f : cava  ‹A, B› ‹C, D›) (g: cava ‹D, E› ‹F, G›) 
                 (input : @signal T ‹A,  ‹B, E››) :
                 cava  ‹A,  ‹B, E››  ‹‹C, F›, G›
  := Reshape (@belowReorg1 A B E) ⟼ first f ⟼ Reshape (@belowReorg2 C D E) ⟼ second g ⟼ Reshape (@belowReorg3 C F G).
           