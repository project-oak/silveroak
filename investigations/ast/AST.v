(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
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
Require Import Coq.Numbers.DecimalString.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Cava.Util.List.
Import ListNotations.

(**** Type system ****)

Inductive SignalType :=
| Bit : SignalType
| Nat : SignalType
.

(* one or more signals *)
Inductive type : Type :=
| tzero
| tone (t : SignalType)
| tpair (t1 t2 : type)
.

(* combines two types while not duplicating tzero values *)
Definition tpair_min (t1 t2 : type) : type :=
  match t1, t2 with
  | tzero, t2 => t2
  | t1, tzero => t1
  | t1, t2 => tpair t1 t2
  end.

(* Notation for signals and collections of signals *)
Declare Scope signal_scope.
Delimit Scope signal_scope with signal.
Bind Scope signal_scope with type.
Coercion tone : SignalType >-> type.
Infix "*" := tpair : signal_scope.
Infix "**" := tpair_min (at level 40) : signal_scope. (* use ** for a pair with no extra Voids *)
Local Notation Void := tzero.

Definition sdenote : Type := SignalType -> Type.
Existing Class sdenote.

(* denotation of a type based on the interpretation of a SignalType *)
Fixpoint denote_type {denote_signal : sdenote} (t : type) : Type :=
  match t with
  | tzero => unit
  | tone t => denote_signal t
  | tpair t1 t2 => denote_type t1 * denote_type t2
  end.

(* type interpretation for Coq semantics *)
Instance signal : sdenote :=
  fun (t: SignalType) =>
    match t with
    | Bit => bool
    | Nat => nat
    end.
Definition value : type -> Type := @denote_type signal.

(* type interpretation for netlist semantics *)
Inductive Signal : SignalType -> Type :=
| BitNet : N -> Signal Bit
| NatNet : N -> Signal Nat
.
Instance denoteSignal : sdenote := Signal.
Definition denoteType : type -> Type := @denote_type Signal.

(* get default values based on default signals *)
Fixpoint default {denote_signal : sdenote}
         (default_signal : forall t, denote_signal t) (t: type)
  : denote_type t :=
  match t as t return denote_type t with
  | tzero => tt
  | tone t => default_signal t
  | tpair t1 t2 => (default default_signal t1, default default_signal t2)
  end.

(* default signals for Coq interpretation *)
Definition default_signal (t: SignalType) : signal t :=
  match t with
  | Bit => false
  | Nat => 0
  end.
Definition default_value (t : type) : value t := default default_signal t.

(* default signals for netlist interpretation *)
Definition default_Signal (t: SignalType) : Signal t :=
  match t with
  | Bit => BitNet 0
  | Nat => NatNet 0
  end.
Definition default_Value (t : type) : denoteType t := default default_Signal t.

(* Create and destruct ** pairs (= pairs without extra Void types) *)
Definition tprod_min {t1 t2 : type} {denote_signal : sdenote}
  : denote_type t1 -> denote_type t2 -> denote_type (t1 ** t2) :=
  match t1, t2 with
  | tzero, _ => fun _ y => y
  | _, tzero => fun x _ => x
  | _,_ => fun x y => (x,y)
  end.
Definition tsplit {t1 t2 : type} {denote_signal : sdenote}
  : denote_type (t1 ** t2) -> denote_type t1 * denote_type t2 :=
  match t1, t2 with
  | tzero, _ => fun x => (tt, x)
  | _, tzero => fun x => (x, tt)
  | _, _ => fun x => x
  end.

(**** Type casting ****)

Definition typecast (s d : type) :=
  forall denote_signal : sdenote, denote_type s -> denote_type d.
Existing Class typecast.

(* this is an identity function but makes the typechecker happy *)
Instance drop_void_r {t : type} : typecast (t ** Void) t :=
  fun _ =>
    match t with
    | tzero => fun x => x
    | _ => fun x => x
    end.
(* this is an identity function but makes the typechecker happy *)
Instance add_void_r {t : type} : typecast t (t ** Void) :=
  fun _ =>
    match t with
    | tzero => fun x => x
    | _ => fun x => x
    end.
Instance tprod_min_cast {t1 t2 : type} : typecast (t1 * t2) (t1 ** t2) :=
  fun _ => uncurry tprod_min.
Instance tsplit_cast {t1 t2 : type} : typecast (t1 ** t2) (t1 * t2) :=
  fun _ => tsplit.
Instance id_cast {t : type} : typecast t t := fun _ x => x.
Instance tprod_min_cast_r {t1 t2 t3 : type} {c:typecast t2 t3} : typecast (t1 * t2) (t1 ** t3) :=
  fun _ x => tprod_min (fst x) (c _ (snd x)).
Instance tsplit_cast_r {t1 t2 t3 : type} {c:typecast t2 t3} : typecast (t1 ** t2) (t1 * t3) :=
  fun _ x => (fst (tsplit x), c _ (snd (tsplit x))).
Instance tprod_min_cast_l {t1 t2 t3 : type} {c:typecast t1 t3} : typecast (t1 * t2) (t3 ** t2) :=
  fun _ x => tprod_min (c _ (fst x)) (snd x).
Instance tsplit_cast_l {t1 t2 t3 : type} {c:typecast t1 t3} : typecast (t1 ** t2) (t3 * t2) :=
  fun _ x => (c _ (fst (tsplit x)), snd (tsplit x)).

(**** Generic Circuit Expressions ****)

(* TODO: use the Abs trick here to get nicer input types *)

Inductive Wires {var : sdenote} : type -> Type :=
(* Reference named wires *)
| Var : forall {t}, denote_type t -> Wires t
(* Constants *)
| ConstNat : nat -> Wires Nat
(* Tuples *)
| Prod : forall {t u}, Wires t -> Wires u -> Wires (t * u)
| Fst : forall {t u}, Wires (t * u) -> Wires t
| Snd : forall {t u}, Wires (t * u) -> Wires u
.

(* A PHOAS-style expression representing a circuit *)
Inductive Circuit {var : sdenote} : type -> type -> type -> Type :=
(* Name and reference wires *)
| Abs : forall {i s t}, (denote_type i -> Circuit Void s t) -> Circuit i s t
| Bind : forall {t u i s1 s2},
    Circuit Void s1 t -> (denote_type t -> Circuit i s2 u) -> Circuit i (s1 ** s2) u
| Ret : forall {t}, Wires t -> Circuit Void Void t
| Apply : forall {s t u}, Circuit t s u -> Wires t -> Circuit Void s u (* TODO: partial application? *)
(* Primitives *)
| Inv : Circuit Bit Void Bit
| And2 : Circuit (Bit * Bit) Void Bit
| AddMod : nat -> Circuit (Nat * Nat) Void Nat
| Comparator : Circuit (Nat * Nat) Void Bit
| Mux2 : Circuit (Bit * (Nat * Nat)) Void Nat
(* type bookkeeping -- only needed for abstract types *)
| Cast :
    forall {i1 i2 s1 s2 t} {icast : typecast i2 i1} {scast : typecast s2 s1} {suncast : typecast s1 s2},
      Circuit i1 s1 t -> Circuit i2 s2 t
(* Registers *)
| Delay : value Nat -> Circuit Nat Nat Nat
| LoopDelay : forall {i o s}, value Nat -> Circuit (Nat * i) s (Nat * o) -> Circuit i (Nat ** s) o
.

(**** Coq semantics and simulation ****)

Fixpoint wvalue {t} (w : @Wires signal t) : value t :=
  match w with
  | Var x => x
  | ConstNat n => n
  | Prod x y => (wvalue x, wvalue y)
  | Fst xy => fst (wvalue xy)
  | Snd xy => snd (wvalue xy)
  end.

(* single-step semantics *)
Fixpoint step {i s o} (c : @Circuit signal i s o)
  : value s -> value i -> value s * value o :=
  match c in Circuit i s o return value s -> value i -> value s * value o with
  | Abs f => fun s i => step (f i) s tt
  | Bind x f =>
    fun s i =>
      let '(xs, fs) := tsplit s in
      let '(xs, xo) := step x xs tt in
      let '(fs, fo) := step (f xo) fs i in
      (tprod_min xs fs, fo)
  | Ret x => fun _ _ => (tt, wvalue x)
  | Apply f x => fun s _ => step f s (wvalue x)
  | Inv => fun _ i => (tt, negb i)
  | And2 => fun _ '(a,b) => (tt, andb a b)
  | AddMod n => fun _ '(a,b) => (tt, (a + b) mod (2 ^ n))
  | Comparator => fun _ '(a,b) => (tt, a <? b)
  | Mux2 => fun _ '(sel,(a,b)) => (tt, if sel then b else a)
  | @Cast _ _ _ _ _ _ icast scast suncast x =>
    fun s i =>
      let '(s, o) := step x (scast _ s) (icast _ i) in
      (suncast _ s, o)
  | Delay _ => fun s i => (i, s)
  | LoopDelay _ x =>
    fun s i =>
      let '(r, xs) := tsplit s in
      let '(xs, xo) := step x xs (r, i) in
      let '(r, o) := xo in
      (tprod_min (t1:=Nat) r xs, o)
  end.

Fixpoint reset_state {i s o} (c : @Circuit signal i s o) : value s :=
  match c in Circuit i s o return value s with
  | Abs f => reset_state (f (default_value _))
  | Bind x f => tprod_min (reset_state x) (reset_state (f (default_value _)))
  | Apply f x => reset_state f
  | @Cast _ _ _ _ _ _ _ _ suncast x => suncast _ (reset_state x)
  | Delay r => r
  | LoopDelay r x => tprod_min r (reset_state x)
  | _ => tt
  end.

Definition simulate {i s o} (c : @Circuit signal i s o) (input : list (value i)) : list (value o) :=
  fold_left_accumulate (step c) input (reset_state c).

(**** Netlist interpretation ****)

Module Netlist.
  (* The nodes of the circuit graph. *)
  Inductive Instance :=
  | Inv : N -> N -> N -> Instance
  | And2 : N -> N -> N -> N -> Instance
  | AddMod : nat -> N -> N -> N -> Instance
  | NatDelay : N -> N -> Instance
  | AssignNat : N -> N -> Instance
  | ConstNat : N -> N -> Instance
  | Comparator : N -> N -> N -> Instance
  | Mux2 : N -> N -> N -> N -> Instance
  .

  Inductive Port :=
  | InputBit : string -> N -> Port
  | OutputBit : N -> string -> Port
  | InputNat : string -> N -> Port
  | OutputNat : N -> string -> Port.

  Record Netlist :=
    mkNetlist {
        netlistName : string; (* Name of the module to be generated. *)
        instCount : N; (* A count of the number of nodes. *)
        bitCount : N; (* A count of the number of local bit-type wires. *)
        natCount : N; (* A count of the number of nat-type wires. *)
        instances : list Instance; (* A list of the circuit graph nodes. *)
        ports : list Port; (* The I/O interface of the circuit. *)
      }.
  (* An empty netlist. *)
  Definition empty (name : string) : Netlist :=
    mkNetlist name 0 0 0 [] [].

  Definition signal_nr {t} (x : Signal t) : N :=
    match x with
    | BitNet n => n
    | NatNet n => n
    end.
  Instance sindex : sdenote := (fun _ => N).
  Definition indices : type -> Type := @denote_type sindex.
  Fixpoint as_indices {t : type} : denoteType t -> indices t :=
    match t as t return denoteType t -> indices t with
    | tzero => fun x => x
    | tone t => signal_nr
    | tpair t1 t2 =>
      fun x =>
        (as_indices (fst x), as_indices (snd x))
    end.

  Definition newNat (net : Netlist) : Netlist * N :=
    match net with
    | mkNetlist name ic bc nc insts ports =>
      (mkNetlist name ic bc (nc + 1) insts ports, nc)
    end.
  Definition newBit (net : Netlist) : Netlist * N :=
    match net with
    | mkNetlist name ic bc nc insts ports =>
      (mkNetlist name ic (bc + 1) nc insts ports, bc)
    end.
  Definition newInstNr (net : Netlist) : Netlist * N :=
    match net with
    | mkNetlist name ic bc nc insts ports =>
      (mkNetlist name (ic + 1) bc nc insts ports, ic)
    end.
  Definition addInstance (net : Netlist) (i : Instance) : Netlist :=
    match net with
    | mkNetlist name ic bc nc insts ports => mkNetlist name ic bc nc (i :: insts) ports
    end.
  Definition addPort (net : Netlist) (p : Port) : Netlist :=
    match net with
    | mkNetlist name ic bc nc insts ports => mkNetlist name ic bc nc insts (p :: ports)
    end.

  Fixpoint wnet {t} (net : Netlist) (w : @Wires denoteSignal t) : Netlist * denoteType t :=
    match w with
    | Var x => (net, x)
    | AST.ConstNat n =>
      let '(net, i) := newNat net in
      let net := addInstance net (ConstNat i (N.of_nat n)) in
      (net, NatNet i)
    | Prod x y =>
      let '(net, x) := wnet net x in
      let '(net, y) := wnet net y in
      (net, (x, y))
    | Fst xy =>
      let '(net, xy) := wnet net xy in
      (net, fst xy)
    | Snd xy =>
      let '(net, xy) := wnet net xy in
      (net, snd xy)
    end.

  (* interpret the circuit as a collection of netlist instances; given the
     instance numbers of the input ports, produce a list of instances and the
     numbers for the output ports *)
  Fixpoint to_netlist' {i s o}
           (net : Netlist)
           (c : @Circuit denoteSignal i s o)
    : denoteType i -> Netlist * denoteType o :=
    match c in Circuit i s o return denoteType i -> Netlist * denoteType o with
    | Abs f => fun i => to_netlist' net (f i) tt
    | Bind x f =>
      fun i =>
        let '(net, xo) := to_netlist' net x tt in
        to_netlist' net (f xo) i
    | Ret x => fun _ => wnet net x
    | Apply f x =>
      fun i =>
        let '(net, x) := wnet net x in
        to_netlist' net f x
    | AST.Inv =>
      fun i =>
        let in_wire := as_indices i in
        let '(net, out_wire) := newBit net in
        let '(net, nr) := newInstNr net in
        let net := addInstance net (Inv nr in_wire out_wire) in
        (net, BitNet out_wire)
    | AST.And2 =>
      fun i =>
        let a_wire := as_indices (t:=Bit) (fst i) in
        let b_wire := as_indices (t:=Bit) (snd i) in
        let '(net, out_wire) := newBit net in
        let '(net, nr) := newInstNr net in
        let net := addInstance net (And2 nr a_wire b_wire out_wire) in
        (net, BitNet out_wire)
    | AST.AddMod n =>
      fun i =>
        let a_wire := as_indices (t:=Nat) (fst i) in
        let b_wire := as_indices (t:=Nat) (snd i) in
        let '(net, out_wire) := newNat net in
        let net := addInstance net (AddMod n a_wire b_wire out_wire) in
        (net, NatNet out_wire)
    | AST.Comparator =>
      fun i =>
        let a_wire := as_indices (t:=Nat) (fst i) in
        let b_wire := as_indices (t:=Nat) (snd i) in
        let '(net, out_wire) := newBit net in
        let net := addInstance net (Comparator a_wire b_wire out_wire) in
        (net, BitNet out_wire)
    | AST.Mux2 =>
      fun i =>
        let sel_wire := as_indices (t:=Bit) (fst i) in
        let a_wire := as_indices (t:=Nat) (fst (snd i)) in
        let b_wire := as_indices (t:=Nat) (snd (snd i)) in
        let '(net, out_wire) := newNat net in
        let net := addInstance net (Mux2 sel_wire a_wire b_wire out_wire) in
        (net, NatNet out_wire)
    | @Cast _ _ _ _ _ _ icast _ _ x => fun i => to_netlist' net x (icast _ i)
    | Delay r =>
      fun i =>
        let in_wire := as_indices i in
        let '(net, out_wire) := newNat net in
        let net := addInstance net (NatDelay in_wire out_wire) in
        (net, NatNet out_wire)
    | LoopDelay r body =>
      fun i =>
        let '(net, in_feedback_wire) := newNat net in
        let in_feedback : denoteType Nat := NatNet in_feedback_wire in
        let '(net, body_out) := to_netlist' net body (in_feedback, i) in
        let '(out_feedback, out) := body_out in
        let out_feedback_wire := as_indices (t:=Nat) out_feedback in
        let net := addInstance net (NatDelay out_feedback_wire in_feedback_wire) in
        (net, out)
    end.

  Instance sname : sdenote := (fun _ => string).
  Definition port_names : type -> Type := @denote_type sname.

  Definition addInput (net : Netlist) (t : SignalType) (name : string)
    : Netlist * Signal t :=
    match t with
    | Bit =>
      let '(net, wire) := newBit net in
      let net := addPort net (InputBit name wire) in
      (net, BitNet wire)
    | Nat =>
      let '(net, wire) := newNat net in
      let net := addPort net (InputNat name wire) in
      (net, NatNet wire)
    end.

  Fixpoint addInputs (net : Netlist) {t : type}
    : port_names t -> Netlist * denoteType t :=
    match t with
    | tzero => fun _ => (net, tt)
    | tone t => addInput net t
    | tpair t1 t2 =>
      fun names =>
        let '(net, x1) := addInputs net (fst names) in
        let '(net, x2) := addInputs net (snd names) in
        (net, (x1, x2))
    end.

  Definition addOutput (net : Netlist) {t : SignalType} (name : string)
    : Signal t -> Netlist :=
    match t with
    | Bit => fun x => addPort net (OutputBit (signal_nr x) name)
    | Nat => fun x => addPort net (OutputNat (signal_nr x) name)
    end.

  Fixpoint addOutputs (net : Netlist) {t : type}
    : port_names t -> denoteType t -> Netlist :=
    match t with
    | tzero => fun _ _ => net
    | tone _ => addOutput net
    | tpair t1 t2 =>
      fun names x =>
        let net := addOutputs net (fst names) (fst x) in
        let net := addOutputs net (snd names) (snd x) in
        net
    end.

  Record interface {i s o} {c : @Circuit denoteSignal i s o} :=
    { netlist_name : string;
      input_names : port_names i;
      output_names : port_names o }.
  Global Arguments interface {_ _ _} _.
  Global Arguments Build_interface {_ _ _} _.

  Definition to_netlist {i s o} (c : @Circuit denoteSignal i s o) (intf : interface c)
    : Netlist :=
    let net := empty intf.(netlist_name) in
    let '(net, inputs) := addInputs net intf.(input_names) in
    let '(net, outputs) := to_netlist' net c inputs in
    let net := addOutputs net intf.(output_names) outputs in
    net.
End Netlist.

(* Generate SystemVerilog from the netlist *)
Module SystemVerilog.
  Import Netlist.
  Local Open Scope string_scope.

  Fixpoint insertCommas (lines : list string) : string :=
    match lines with
    | [] => ""
    | [x] => x
    | x::xs => x ++ ", " ++ insertCommas xs
    end.

  Definition portDeclaration (p : Port) : string :=
    match p with
    | InputBit name _ => "input logic " ++ name
    | OutputBit _ name => "output logic " ++ name
    | InputNat name _ => "input int unsigned " ++ name
    | OutputNat _ name => "output int unsigned " ++ name
    end.

  Definition portDeclarations := map portDeclaration.

  Definition showN (n : N) : string := NilEmpty.string_of_uint (N.to_uint n).

  Definition declareBitNets (bc : N) : list string :=
    match bc with
    | N0 => []
    | Npos bc' => ["  logic net[0:" ++ showN (bc - 1) ++ "];"]
    end.

  Definition declareNatNets (nc : N) : list string :=
    map (fun i => "  int unsigned nat" ++ showN (N.of_nat i) ++ ";") (seq 0 (N.to_nat nc)).

  Definition declareLocalNets (nl : Netlist) : list string :=
    declareBitNets (bitCount nl) ++ declareNatNets (natCount nl).

  Definition netS (n : N) : string := "net[" ++ showN n ++ "]".

  Definition natS (n : N) : string := "nat" ++ showN n.


  Definition instantiateComponent (component : Instance) : string :=
    match component with
    | Inv instNr i o => "  not not_" ++ showN instNr ++ " (" ++
                                    netS o ++ ", " ++ netS i ++ ");"
    | And2 instNr i0 i1 o => "  and and_" ++ showN instNr ++ " (" ++ netS o ++ ", " ++  netS i0 ++
                                         ", " ++ netS i1 ++ ");"
    | AddMod modVal i0 i1 o => "  assign " ++ natS o ++ " = (" ++ natS i0 ++ " + " ++
                                          natS i1 ++ ") % " ++ showN (N.of_nat modVal) ++ ";"
    | NatDelay i o => "  always_ff @(posedge clk) "
                       ++ natS o ++ " <= rst ? 0 : " ++ natS i ++ ";"
    | AssignNat n v => "  assign " ++ natS n ++ " = " ++ natS v  ++ ";"
    | ConstNat n v => "  assign " ++ natS n ++ " = " ++ showN v ++ ";"
    | Comparator a b cf => "  assign " ++ netS cf ++ " = " ++ natS a ++ " == " ++ natS b ++ ";"
    | Mux2 sel a b o => "  assign " ++ natS o ++ " = " ++ netS sel ++ " ? " ++ natS a ++ " : " ++ natS b ++ ";"
    end.

  Definition instantiateComponents := map instantiateComponent.

  Definition declarePorts (pl : list Port) : string :=
    " (input logic clk, input logic rst, " ++ insertCommas (portDeclarations pl) ++ ")".

  Definition wireUpPort (p : Port) : string :=
    match p with
    | InputBit name i => "  assign " ++ netS i ++ " = " ++ name ++ ";"
    | OutputBit i name => "  assign " ++ name ++ " = " ++ netS i ++ ";"
    | InputNat name i => "  assign " ++ natS i ++ " = " ++ name ++ ";"
    | OutputNat i name => "  assign " ++ name ++ " = " ++ natS i ++ ";"
    end.

  Definition wireUpPorts := map wireUpPort.

  Definition systemVerilogLines (nl : Netlist) : list string :=
    ["module " ++ netlistName nl ++ declarePorts (ports nl) ++ ";";
    "timeunit 1ns; timeprecision 1ns;"] ++
                                        declareLocalNets nl ++
                                        wireUpPorts (ports nl) ++
                                        instantiateComponents (instances nl) ++
                                        ["endmodule"].

  Fixpoint unlines (lines : list string) : string :=
    match lines with
    | [] => ""
    | x::xs => x ++ "\n" ++ unlines xs
    end.

  Definition print {i s o} (c : @Circuit denoteSignal i s o) (intf : interface c) : string :=
    unlines (systemVerilogLines (to_netlist c intf)).
End SystemVerilog.


(**** Notations and setup ****)

Definition Compose {denote_signal : sdenote} {i1 s1 o1 s2 o2}
           (f : Circuit i1 s1 o1) (g : Circuit o1 s2 o2)
  : Circuit i1 (s1 ** s2) o2 :=
  Cast (Abs (fun x => Bind (Apply f (Var x))
                        (fun y => Apply g (Var y)))).

Declare Scope expr_scope.
Delimit Scope expr_scope with expr.
Notation "x <- e1 ;; e2" :=
  (Bind e1 (fun x => let x := Var x in e2))
    (at level 60, e1 at next level, right associativity) : expr_scope.
Notation "f @ x" := (Apply f x) (at level 40, left associativity) : expr_scope.
Notation "f >=> g" :=(Compose f g) (at level 60, right associativity) : expr_scope.
Notation "( x , y , .. , z )" := (Prod .. (Prod x y) .. z) (at level 0) : expr_scope.
Notation "'abs!' x => e" := (Abs (fun y => let x := Var y in e%expr)) (x binder, e constr, at level 199).

(**** Combinators ****)

Section WithDenoteSignal.
  Context {denote_signal : sdenote}.

  Definition fork2 {A} : Circuit A Void (A * A) :=
    Cast (abs! a => Ret (a,a)).

  Definition fsT {A B C s} (f : Circuit A s C) : Circuit (A * B) s (C * B) :=
    Cast (abs! ab =>
          c <- f @ (Fst ab) ;;
          Ret (c, Snd ab)).
  Definition snD {A B C s} (f : Circuit B s C) : Circuit (A * B) s (A * C) :=
    Cast (abs! ab =>
          c <- f @ (Snd ab) ;;
          Ret (Fst ab, c))%expr.
End WithDenoteSignal.

(**** Examples ****)

Local Open Scope string_scope.

Definition nandGate {denote_signal : sdenote} : Circuit (Bit * Bit) Void Bit :=
  (And2 >=> Inv)%expr.

Compute simulate nandGate [(true,true);(true,false);(false,true);(false,false)].

Definition nandGate_interface : Netlist.interface nandGate :=
  Netlist.Build_interface nandGate "nandGate" ("i0", "i1") "o".

Redirect "nandgate.sv" Compute (SystemVerilog.print nandGate nandGate_interface).

Definition addmod6 {denote_signal : sdenote} : Circuit (Nat * Nat) Void Nat := AddMod 6.

Definition addmod6_interface : Netlist.interface addmod6 :=
  Netlist.Build_interface addmod6 "addmod6" ("a", "b") "c".

Redirect "addmod6.sv" Compute (SystemVerilog.print addmod6 addmod6_interface).

Definition delay1 {denote_signal : sdenote} : Circuit Nat Nat Nat := Delay 0.

Definition delay1_interface : Netlist.interface delay1 :=
  Netlist.Build_interface delay1 "delay1" "a" "a1".

Redirect "delay1.sv" Compute (SystemVerilog.print delay1 delay1_interface).

Definition pipe2 {denote_signal : sdenote} : Circuit Nat (Nat * Nat) Nat :=
  (Delay 0 >=> Delay 0)%expr.

Definition pipe2_interface : Netlist.interface pipe2 :=
  Netlist.Build_interface pipe2 "pipe2" "a" "a2".

Redirect "pipe2.sv" Compute (SystemVerilog.print pipe2 pipe2_interface).

Definition counter6 {denote_signal : sdenote} : Circuit Void (Nat * Nat) Nat  :=
  (count6 <- LoopDelay 0 (AddMod 6 >=> Delay 0 >=> fork2) @ (ConstNat 1) ;;
   Ret count6)%expr.

Definition counter6_interface : Netlist.interface counter6 :=
  Netlist.Build_interface counter6 "counter6" tt "count6".

Redirect "counter6.sv" Compute (SystemVerilog.print counter6 counter6_interface).

Definition counter6by4 {denote_signal : sdenote}
  : Circuit Void (Nat * Nat * (Nat * Nat)) Nat :=
  (count4 <- LoopDelay 0 (AddMod 4 >=> Delay 0 >=> fork2) @ (ConstNat 1) ;;
   is3 <- Comparator @ (count4, ConstNat 3) ;;
   incVal <- Mux2 @ (is3, (ConstNat 1, ConstNat 0)) ;;
   count6by4 <- LoopDelay 0 (AddMod 6 >=> Delay 0 >=> fork2) @ incVal ;;
   Ret count6by4)%expr.

Definition counter6by4_interface : Netlist.interface counter6by4 :=
  Netlist.Build_interface counter6by4 "counter6by4" tt "count6by4".

Redirect "counter6by4.sv" Compute (SystemVerilog.print counter6by4 counter6by4_interface).

Definition nestedloop {denote_signal : sdenote}
  : Circuit Void (Nat * (Nat * (Nat * Nat))) Nat :=
  (o <- LoopDelay 0 (snD (Delay 0) >=> AddMod 512
                        >=> LoopDelay 0 (AddMod 512 >=> Delay 0 >=> fork2) >=> fork2) @ ConstNat 1 ;;
   Ret o)%expr.

Definition nestedloop_interface : Netlist.interface nestedloop :=
  Netlist.Build_interface nestedloop "nestedloop" tt "count6by4".

Redirect "nestedloop.sv" Compute (SystemVerilog.print nestedloop nestedloop_interface).

(* inputs can be placed inside loop expressions instead of fed in separately *)
Definition input_in_loop {denote_signal : sdenote}
  : Circuit (Bit * Nat) Nat Nat :=
  (LoopDelay 0 (abs! (input : Wires (Nat * (Bit * Nat))) =>
                let x := Fst input in
                let sel := Fst (Snd input) in
                let y := Snd (Snd input) in
                sel <- (Inv >=> Inv) @ sel ;;
                x' <- Mux2 @ (sel, (y, x)) ;;
                fork2 @ x'))%expr.

Compute simulate input_in_loop (combine [true;false;true;false;true;false;true;false] (seq 0 8)).

Definition input_in_loop_interface : Netlist.interface input_in_loop :=
  Netlist.Build_interface input_in_loop "input_in_loop" ("sel", "y") "x".

Redirect "input_in_loop.sv" Compute (SystemVerilog.print input_in_loop input_in_loop_interface).


(**** Proofs ****)
