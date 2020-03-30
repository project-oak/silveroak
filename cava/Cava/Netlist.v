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

(* A codification of the Lava embedded DSL develope for Haskell into
   Coq for the specification, implementaiton and formal verification of circuits.
   Experimental work, very much in flux, as Satnam learns Coq!
*)

Require Import Program.Basics.
From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import ZArith.
From Coq Require Import Lists.List.
From Coq Require Import Vector.
From Coq Require Import Numbers.NaryFunctions.
Import ListNotations.

(******************************************************************************)
(* Primitive elements                                                         *)
(******************************************************************************)

(* The primitive elements that can be instantiated in Cava. Some are generic
   SystemVerilog gates that can be used with synthesis and back-end tools to
   map to any architecture, while others are specific to Xilinx FPGAs.
*)

Inductive Primitive :=
  (* SystemVerilog primitive gates. *)
  | Not  : N -> N -> Primitive
  | And  : list N -> N -> Primitive
  | Nand : list N -> N -> Primitive
  | Or   : list N -> N -> Primitive
  | Nor  : list N -> N -> Primitive
  | Xor  : list N -> N -> Primitive
  | Xnor : list N -> N -> Primitive
  | Buf  : N -> N -> Primitive
  (* A Cava unit delay bit component. *)
  | DelayBit : N -> N -> Primitive
  (* Assignment of bit wire *)
  | AssignBit : N -> N -> Primitive
  (* Mapping to SystemVerilog vectors *)
  | ToVec : forall n, Vector.t N n -> N -> Primitive (* Maps bitvec to SV vec *)
  | FromVec : forall n, N -> Vector.t N n -> Primitive (* Maps SV vec to bitvec *)
  (* Arithmetic operations *)
  | UnsignedAdd : N -> N -> N -> Primitive
  (* Xilinx FPGA architecture specific gates. *)
  | Xorcy : N -> N -> N -> Primitive
  | Muxcy : N -> N -> N -> N -> Primitive.

(******************************************************************************)
(* Data structures to represent circuit graph/netlist state                   *)
(******************************************************************************)

Inductive PortType :=
  | BitPort : N -> PortType
  | VectorTo0Port : forall n, Vector.t N n -> PortType
  | VectorFrom0Port : forall n, Vector.t N n  -> PortType.

Record PortDeclaration : Type := mkPort {
  port_name : string;
  port_type : PortType;
}.

Notation Netlist := (list Primitive).

Record Module : Type := mkModule {
  moduleName : string;
  netlist : Netlist;
  inputs : list PortDeclaration;
  outputs : list PortDeclaration;
}.

Record CavaState : Type := mkCavaState {
  netNumber : N;
  vecNumber : N;
  isSequential : bool;
  module : Module;
}.

(******************************************************************************)
(* The initial empty netlist                                                  *)
(******************************************************************************)

(* Net number 0 carries the constant signal zero. Net number 1 carries the
   constant signal 1. We start numbering from 2 for the user nets.
*)

Definition initStateFrom (startAt : N) : CavaState
  := mkCavaState startAt 0 false (mkModule "" [] [] []).

Definition initState : CavaState
  := initStateFrom 2.



Section Netlang.
  Inductive type :=
  | Hole : type
  | Prim : type
  | Mod  : type
  | PortDecl: type
  | List : type -> type
  | Func : type -> type -> type.

  Variable var: type ->  Type.

  Inductive term : type -> Type :=
  | Const : N -> term Hole
  | Var : forall x, var x -> term x
  | Abs : forall x y, (var x -> term y) -> term (Func x y)
  | App : forall x y, term (Func x y) -> term x -> term y

  | Prim2 : (N -> N -> Primitive) -> term Hole -> term Hole -> term Prim
  | Prim3 : (N -> N -> N -> Primitive) -> term Hole -> term Hole -> term Hole -> term Prim
  | Prim4 : (N -> N -> N -> N -> Primitive) -> term Hole -> term Hole -> term Hole -> term Hole -> term Prim
  | Prim': (list N -> Primitive) -> term (List Hole) -> term Prim

  | LiftList : forall x, list (term x) -> term (List x)
  | Module' : string -> term (List Prim) -> term (List PortDecl) -> term (List PortDecl) -> term Mod
  | Port' : string -> term Hole -> term PortDecl.
End Netlang.

Arguments Var _ [x] _.
Arguments Abs _ [x y] _.
Arguments App _ [x y] _.

Arguments Const [var].

Arguments Prim2 [var].
Arguments Prim3 [var].
Arguments Prim4 [var].
Arguments Prim' [var].

Arguments LiftList [var x].
Arguments Module' [var].
Arguments Port' [var].

Fixpoint denoteType t :=
match t with
| Hole => N
| Prim => Primitive
| Mod => Module
| PortDecl => PortDeclaration
| List t => list (denoteType t)
| Func t1 t2 => denoteType t1 -> denoteType t2
end.

Fixpoint denoteTerm t (e: term denoteType t) : denoteType t :=
let dt := denoteTerm in
match e in term _ t return denoteType t with
| Var _ x => x
| Abs _ f => fun x => dt _ (f x)
| App _ f x => (dt _ f) (dt _ x)
| Const x => x
| Prim2 p x y => p (dt _ x) (dt _ y)
| Prim3 p x y z => p (dt _ x) (dt _ y) (dt _ z)
| Prim4 p x y z w => p (dt _ x) (dt _ y) (dt _ z) (dt _ w)
| Prim' p xs => p (dt _ xs)
| LiftList xs => (List.map (dt _) xs)
| Module' name nl is os => mkModule name (dt _ nl) (dt _ is) (dt _ os)
| Port' name x => mkPort name (BitPort (dt _ x))
end.

Fixpoint substitute' var t (e: term (term var) t): term var t :=
let r := substitute' in
match e with
| Var _ x => x
| Abs _ f => Abs _ (fun x => r _ _ (f (Var _ x)))
| App _ f x => App _ (r _ _ f) (r _ _ x)
| Const x => Const x
| Prim2 p x y => Prim2 p (r _ _ x)(r _ _ y)
| Prim3 p x y z => Prim3 p (r _ _ x) (r _ _ y) (r _ _ z)
| Prim4 p x y z w => Prim4 p (r _ _ x) (r _ _ y) (r _ _ z) (r _ _ w)
| Prim' p xs => Prim' p (r _ _ xs)
| LiftList xs => LiftList (List.map (r _ _) xs)
| Module' name nl is os => Module' name (r _ _ nl) (r _ _ is) (r _ _ os)
| Port' name x => Port' name (r _ _ x)
end.

Definition Term t := forall var, term var t.
Definition Term1 t1 t2 := forall var, var t1 -> term var t2.

Definition substitute t1 t2 (e1: Term1 t1 t2) (e2: Term t1) : Term t2 :=
fun var => substitute' _ _ (e1 (term var) (e2 var)).

(*
Takes an `NaryFunction` `N ^^ n --> B`, that has n arguments of type N returning type B.
Automatically applies incrementing values of N starting at a. 
e.g. if f :  A ^^ n --> B
then autoNumber' _ 0 5 f == f 0 1 2 3 4
*)
Fixpoint autoNumber' (B:Type) (a:N) n : (N^^n-->B) -> B :=
 match n return (N^^n-->B) -> B with
  | O => fun x => x
  | S n => fun x => autoNumber' B (a+1) n (x a)
 end.

Fixpoint autoNumber n t (f: nfun N n t) : t :=
autoNumber' t (2%N) n f.

Fixpoint countHoles t :=
match t with
| Func Hole t2 => 1 + countHoles t2
| _ => 0
end.

Fixpoint CountHoles var t (_: term var t) := countHoles t.

(* a netlist only to demonstrate arbitrary connections, the circuit itself is meaningless *)
Example example_netlist var
:= Abs var (fun x => Abs _ (fun y => Abs _ (fun w => Abs _ (fun z =>
LiftList
[ Prim2 Buf (Var _ x) (Var _ x)
; Prim2 Buf (Var _ x) (Var _ y)
; Prim2 Buf (Var _ y) (Var _ x)
; Prim2 Buf (Var _ y) (Var _ y)
; Prim2 Not (Var _ z) (Var _ w)
; Prim2 Not (Var _ y) (Var _ z)
]
)))).

Example netlist_denote_then_apply := denoteTerm _ (example_netlist _) 2%N 3%N 4%N 5%N.
Example netlist_autonumber := autoNumber 4 _ (denoteTerm _ (example_netlist _)).
Example netlist_countholes_autonumber := 
  let ex := (example_netlist _)
  in autoNumber (CountHoles _ _ ex) _ (denoteTerm _ ex).
