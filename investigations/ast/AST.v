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
| Void : SignalType
| Bit : SignalType
| Nat : SignalType
.

(* one or more signals *)
Inductive type : Type :=
| tone (t : SignalType)
| tpair (t1 t2 : type)
.

(* combines two types while not duplicating Void values *)
Definition tpair_min (t1 t2 : type) : type :=
  match t1, t2 with
  | tone Void, t2 => t2
  | t1, tone Void => t1
  | t1, t2 => tpair t1 t2
  end.

(* Notation for signals and collections of signals *)
Declare Scope signal_scope.
Delimit Scope signal_scope with signal.
Bind Scope signal_scope with type.
Coercion tone : SignalType >-> type.
Infix "*" := tpair : signal_scope.
Infix "**" := tpair_min (at level 40) : signal_scope. (* use ** for a pair with no extra Voids *)

(* denotation of a type based on the interpretation of a SignalType *)
Fixpoint denote_type (denote_signal : SignalType -> Type) (t : type) : Type :=
  match t with
  | tone t => denote_signal t
  | tpair t1 t2 => denote_type denote_signal t1 * denote_type denote_signal t2
  end.

(* type interpretation for Coq semantics *)
Definition signal (t: SignalType) : Type :=
  match t with
  | Void => unit
  | Bit => bool
  | Nat => nat
  end.
Definition value : type -> Type := denote_type signal.

(* type interpretation for netlist semantics *)
Inductive Signal : SignalType -> Type :=
| Undefined : Signal Void
| BitNet : N -> Signal Bit
| NatNet : N -> Signal Nat
.
Definition denoteSignal (t: SignalType) : Type := Signal t.
Definition denoteType : type -> Type := denote_type denoteSignal.

(* get default values based on default signals *)
Fixpoint default {denote_signal : SignalType -> Type}
         (default_signal : forall t, denote_signal t) (t: type)
  : denote_type denote_signal t :=
  match t as t return denote_type denote_signal t with
  | tone t => default_signal t
  | tpair t1 t2 => (default default_signal t1, default default_signal t2)
  end.

(* default signals for Coq interpretation *)
Definition default_signal (t: SignalType) : signal t :=
  match t with
  | Void => tt
  | Bit => false
  | Nat => 0
  end.
Definition default_value (t : type) : value t := default default_signal t.

(* default signals for netlist interpretation *)
Definition default_Signal (t: SignalType) : Signal t :=
  match t with
  | Void => Undefined
  | Bit => BitNet 0
  | Nat => NatNet 0
  end.
Definition default_Value (t : type) : denoteType t := default default_Signal t.

(* Create and destruct ** pairs (= pairs without extra Void types) *)
Definition tprod_min {t1 t2 : type} {denote_signal}
  : denote_type denote_signal t1 -> denote_type denote_signal t2
    -> denote_type denote_signal (t1 ** t2) :=
  match t1, t2 with
  | tone Void, _ => fun _ y => y
  | _, tone Void => fun x _ => x
  | _,_ => fun x y => (x,y)
  end.
Definition tsplit {t1 t2 : type} {denote_signal}
           (void : denote_signal Void)
  : denote_type denote_signal (t1 ** t2)
    -> denote_type denote_signal t1 * denote_type denote_signal t2 :=
  match t1, t2 with
  | tone Void, _ => fun x => (void, x)
  | _, tone Void => fun x => (x, void)
  | _, _ => fun x => x
  end.

(**** Generic Circuit Expressions ****)

(* A PHOAS-style expression representing a circuit *)
Inductive CircuitExpr {var : type -> Type} : type -> type -> type -> Type :=
(* Name and reference wires *)
| Var : forall {t}, var t -> CircuitExpr Void Void t
| Input : forall t, CircuitExpr t Void t
| Bind : forall {t u i1 i2 s1 s2},
    CircuitExpr i1 s1 t -> (var t -> CircuitExpr i2 s2 u) -> CircuitExpr (i1 ** i2) (s1 ** s2) u
| Apply : forall {i s1 s2 t u}, CircuitExpr t s2 u -> CircuitExpr i s1 t -> CircuitExpr i (s1 ** s2) u
(* Constants *)
| ConstNat : nat -> CircuitExpr Void Void Nat
(* Primitives *)
| Inv : forall {i s}, CircuitExpr i s Bit -> CircuitExpr i s Bit
| And2 : forall {i s}, CircuitExpr i s (Bit * Bit) -> CircuitExpr i s Bit
| AddMod : forall {i s}, nat -> CircuitExpr i s (Nat * Nat) -> CircuitExpr i s Nat
| Compare : forall {i s}, CircuitExpr i s (Nat * Nat) -> CircuitExpr i s Bit
| Mux2 : forall {i s}, CircuitExpr i s (Bit * (Nat * Nat)) -> CircuitExpr i s Nat
(* Tuples *)
| Prod : forall {t u i1 i2 s1 s2},
    CircuitExpr i1 s1 t -> CircuitExpr i2 s2 u -> CircuitExpr (i1 ** i2) (s1 ** s2) (t * u)
| Fst : forall {t u i s}, CircuitExpr i s (t ** u) -> CircuitExpr i s t
| Snd : forall {t u i s}, CircuitExpr i s (t ** u) -> CircuitExpr i s u
(* Registers *)
| Delay : forall {i s}, value Nat -> CircuitExpr i s Nat -> CircuitExpr i (Nat ** s) Nat
| LoopDelay : forall {i o s}, value Nat -> (var Nat -> CircuitExpr i s (Nat ** o)) -> CircuitExpr i (Nat ** s) o
.
Global Arguments CircuitExpr : clear implicits.

Definition Circuit i s o : Type := forall var, CircuitExpr var i s o.

(**** Coq semantics and simulation ****)

(* single-step semantics *)
Fixpoint step {i s o} (c : CircuitExpr value i s o)
  : value s -> value i -> value s * value o :=
  match c in CircuitExpr _ i s o return value s -> value i -> value s * value o with
  | Var x => fun s _ => (s, x)
  | Input t => fun _ i => (tt, i)
  | Bind x f =>
    fun s i =>
      let '(xs, fs) := tsplit tt s in
      let '(xi, fi) := tsplit tt i in
      let '(xs, xo) := step x xs xi in
      let '(fs, fo) := step (f xo) fs fi in
      (tprod_min xs fs, fo)
  | Apply f x =>
    fun s i =>
      let '(xs, fs) := tsplit tt s in
      let '(xs, xo) := step x xs i in
      let '(fs, fo) := step f fs xo in
      (tprod_min xs fs, fo)
  | ConstNat x => fun _ _ => (tt, x)
  | Inv x =>
    fun s i =>
      let '(s, o) := step x s i in
      (s, negb o)
  | And2 x =>
    fun s i =>
      let '(s, (a, b)) := step x s i in
      (s, andb a b)
  | AddMod n x =>
    fun s i =>
      let '(s, (a, b)) := step x s i in
      (s, (a + b) mod (2 ^ n))
  | Compare x =>
    fun s i =>
      let '(s, (a, b)) := step x s i in
      (s, (a <? b))
  | Mux2 x =>
    fun s i =>
      let '(s, (sel, (a, b))) := step x s i in
      (s, if sel then b else a)
  | Prod x y =>
    fun s i =>
      let '(xs, ys) := tsplit tt s in
      let '(xi, yi) := tsplit tt i in
      let '(xs, xo) := step x xs xi in
      let '(ys, yo) := step y ys yi in
      (tprod_min xs ys, (xo, yo))
  | Fst x =>
    fun s i =>
      let '(s, xo) := step x s i in
      (s, fst (tsplit tt xo))
  | Snd x =>
    fun s i =>
      let '(s, xo) := step x s i in
      (s, snd (tsplit tt xo))
  | Delay _ x =>
    fun s i =>
      let '(s, xs) := tsplit tt s in
      let '(xs, xo) := step x xs i in
      (tprod_min xo xs, s)
  | LoopDelay _ x =>
    fun s i =>
      let '(r, xs) := tsplit tt s in
      let '(xs, xo) := step (x r) xs i in
      let '(r, o) := tsplit tt xo in
      (tprod_min r xs, o)
  end.

Fixpoint reset_state {i s o} (c : CircuitExpr value i s o) : value s :=
  match c in CircuitExpr _ i s o return value s with
  | Bind x f => tprod_min (reset_state x) (reset_state (f (default_value _)))
  | Apply f x => tprod_min (reset_state x) (reset_state f)
  | Inv x => reset_state x
  | And2 x => reset_state x
  | AddMod _ x => reset_state x
  | Compare x => reset_state x
  | Mux2 x => reset_state x
  | Prod x y => tprod_min (reset_state x) (reset_state y)
  | Fst x => reset_state x
  | Snd x => reset_state x
  | Delay r x => tprod_min r (reset_state x)
  | LoopDelay r x => tprod_min r (reset_state (x (default_value _)))
  | _ => tt
  end.

Definition simulate {i s o} (c : CircuitExpr value i s o) (input : list (value i)) : list (value o) :=
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
  | Compare : N -> N -> N -> Instance
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
    | Undefined => 0
    | BitNet n => n
    | NatNet n => n
    end.
  Definition indices : type -> Type := denote_type (fun _ => N).
  Fixpoint as_indices {t : type} : denoteType t -> indices t :=
    match t as t return denoteType t -> indices t with
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

  (* interpret the circuit as a collection of netlist instances; given the
     instance numbers of the input ports, produce a list of instances and the
     numbers for the output ports *)
  Fixpoint to_netlist' {i s o}
           (net : Netlist)
           (c : CircuitExpr denoteType i s o)
    : denoteType i -> Netlist * denoteType o :=
    match c in CircuitExpr _ i s o return denoteType i -> Netlist * denoteType o with
    | Var x => fun _ => (net, x)
    | Input t => fun x => (net, x)
    | Bind x f =>
      fun i =>
        let '(xi, fi) := tsplit Undefined i in
        let '(net, xo) := to_netlist' net x xi in
        to_netlist' net (f xo) fi
    | Apply f x =>
      fun i =>
        let '(net, xo) := to_netlist' net x i in
        to_netlist' net f xo
    | AST.ConstNat x =>
      fun _ =>
        let '(net, i) := newNat net in
        let net := addInstance net (ConstNat i (N.of_nat x)) in
        (net, NatNet i)
    | AST.Inv x =>
      fun i =>
        let '(net, input) := to_netlist' net x i in
        let in_wire := as_indices input in
        let '(net, out_wire) := newBit net in
        let '(net, nr) := newInstNr net in
        let net := addInstance net (Inv nr in_wire out_wire) in
        (net, BitNet out_wire)
    | AST.And2 x =>
      fun i =>
        let '(net, (a, b)) := to_netlist' net x i in
        let a_wire := as_indices (t:=Bit) a in
        let b_wire := as_indices (t:=Bit) b in
        let '(net, out_wire) := newBit net in
        let '(net, nr) := newInstNr net in
        let net := addInstance net (And2 nr a_wire b_wire out_wire) in
        (net, BitNet out_wire)
    | AST.AddMod n x =>
      fun i =>
        let '(net, (a, b)) := to_netlist' net x i in
        let a_wire := as_indices (t:=Nat) a in
        let b_wire := as_indices (t:=Nat) b in
        let '(net, out_wire) := newNat net in
        let net := addInstance net (AddMod n a_wire b_wire out_wire) in
        (net, NatNet out_wire)
    | AST.Compare x =>
      fun i =>
        let '(net, (a, b)) := to_netlist' net x i in
        let a_wire := as_indices (t:=Nat) a in
        let b_wire := as_indices (t:=Nat) b in
        let '(net, out_wire) := newBit net in
        let net := addInstance net (Compare a_wire b_wire out_wire) in
        (net, BitNet out_wire)
    | AST.Mux2 x =>
      fun i =>
        let '(net, (sel, (a, b))) := to_netlist' net x i in
        let sel_wire := as_indices (t:=Bit) sel in
        let a_wire := as_indices (t:=Nat) a in
        let b_wire := as_indices (t:=Nat) b in
        let '(net, out_wire) := newNat net in
        let net := addInstance net (Mux2 sel_wire a_wire b_wire out_wire) in
        (net, NatNet out_wire)
    | Prod x y =>
      fun i =>
        let '(xi, yi) := tsplit Undefined i in
        let '(net, xo) := to_netlist' net x xi in
        let '(net, yo) := to_netlist' net y yi in
        (net, (xo, yo))
    | Fst x =>
      fun i =>
        let '(net, xo) := to_netlist' net x i in
        (net, fst (tsplit Undefined xo))
    | Snd x =>
      fun i =>
        let '(net, xo) := to_netlist' net x i in
        (net, snd (tsplit Undefined xo))
    | Delay r x =>
      fun i =>
        let '(net, input) := to_netlist' net x i in
        let in_wire := as_indices input in
        let '(net, out_wire) := newNat net in
        let net := addInstance net (NatDelay in_wire out_wire) in
        (net, NatNet out_wire)
    | LoopDelay r body =>
      fun i =>
        let '(net, in_feedback_wire) := newNat net in
        let '(net, body_out) := to_netlist' net (body (NatNet in_feedback_wire)) i in
        let '(out_feedback, out) := tsplit Undefined body_out in
        let out_feedback_wire := as_indices out_feedback in
        let net := addInstance net (NatDelay out_feedback_wire in_feedback_wire) in
        (net, out)
    end.

  Definition port_names : type -> Type := denote_type (fun _ => string).

  Definition addInput (net : Netlist) (t : SignalType) (name : string)
    : Netlist * denoteSignal t :=
    match t with
    | Bit =>
      let '(net, wire) := newBit net in
      let net := addPort net (InputBit name wire) in
      (net, BitNet wire)
    | Nat =>
      let '(net, wire) := newNat net in
      let net := addPort net (InputNat name wire) in
      (net, NatNet wire)
    | Void =>
      (* No need to add an actual port for void input *)
      (net, Undefined)
    end.

  Fixpoint addInputs (net : Netlist) {t : type}
    : port_names t -> Netlist * denoteType t :=
    match t with
    | tone t => addInput net t
    | tpair t1 t2 =>
      fun names =>
        let '(net, x1) := addInputs net (fst names) in
        let '(net, x2) := addInputs net (snd names) in
        (net, (x1, x2))
    end.

  Definition addOutput (net : Netlist) {t : SignalType} (name : string)
    : denoteSignal t -> Netlist :=
    match t with
    | Bit => fun x => addPort net (OutputBit (signal_nr x) name)
    | Nat => fun x => addPort net (OutputNat (signal_nr x) name)
    | Void =>
      (* No need to add an actual port for void output *)
       fun _ => net
    end.

  Fixpoint addOutputs (net : Netlist) {t : type}
    : port_names t -> denoteType t -> Netlist :=
    match t with
    | tone t => addOutput net
    | tpair t1 t2 =>
      fun names x =>
        let net := addOutputs net (fst names) (fst x) in
        let net := addOutputs net (snd names) (snd x) in
        net
    end.

  Record interface {i s o} {c : Circuit i s o} :=
    { netlist_name : string;
      input_names : port_names i;
      output_names : port_names o }.
  Global Arguments interface {_ _ _} _.
  Global Arguments Build_interface {_ _ _} _.

  Definition to_netlist {i s o} (c : Circuit i s o) (intf : interface c)
    : Netlist :=
    let net := empty intf.(netlist_name) in
    let '(net, inputs) := addInputs net intf.(input_names) in
    let '(net, outputs) := to_netlist' net (c _) inputs in
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
    | Compare a b cf => "  assign " ++ netS cf ++ " = " ++ natS a ++ " == " ++ natS b ++ ";"
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

  Definition print {i s o} (c : Circuit i s o) (intf : interface c) : string :=
    unlines (systemVerilogLines (to_netlist c intf)).
End SystemVerilog.






(**** Examples ****)

Local Open Scope string_scope.

Definition test : Circuit Nat Void (Nat * Nat) :=
  fun var => Bind (Input Nat) (fun x => Prod (Var x) (Var x)).
Definition test2 : Circuit Nat Nat (Nat * Nat) :=
  fun var =>
    Bind (Input (Nat))
         (fun x =>
            Bind (Delay 0 (Var x))
                 (fun y => Prod (Var x) (Var y))).
Definition test2_interface : Netlist.interface test2 :=
  Netlist.Build_interface test2 "test2" "i0" ("o0", "o1").
Compute simulate (test2 _) (seq 0 3).
Check Netlist.interface.
Compute SystemVerilog.print test2 test2_interface.

Declare Scope expr_scope.
Delimit Scope expr_scope with expr.
Notation "x <- e1 ;; e2" :=
  (Bind e1 (fun x => let x := Var x in e2))
    (at level 60, e1 at next level, right associativity) : expr_scope.
(*
Notation "e1 >=> e2" :=
  (fun x => Bind (e1 x) e2)
    (at level 60, right associativity) : expr_scope.
Check ((AddMod 6) >=> Delay 0)%expr.*)
Definition Compose {var i s1 s2 o1 o2}
           (c1 : CircuitExpr var i s1 o1)
           (c2 : CircuitExpr var o1 s2 o2)
  : CircuitExpr var i (s1 ** s2) o2 :=
  Apply c2 c1.
Notation "f >=> g" :=
  (fun x => Compose f g) (at level 60, right associativity) : expr_scope.
Check ((AddMod 6 _) >=> Delay 0 _)%expr.
Notation "( x , y , .. , z )" :=
  (Prod .. (Prod x y) .. z) (at level 0) : expr_scope.

Notation "'circuit' x" := (fun var => x%expr) (at level 40, only parsing).

Definition nandGate : Circuit (Bit * Bit) Void Bit :=
  circuit
    (i0 <- Input Bit ;;
     i1 <- Input Bit ;;
     o1 <- And2 (i0, i1) ;;
     Inv o1).

Definition nandGate_interface : Netlist.interface nandGate :=
  Netlist.Build_interface nandGate "nandGate" ("i0", "i1") "o".

Redirect "nandgate.sv" Compute (SystemVerilog.print nandGate nandGate_interface).

Definition addmod : Circuit (Nat * Nat) Void Nat :=
  circuit
    (a <- Input Nat ;;
     b <- Input Nat ;;
     AddMod 6 (a, b)).

Definition addmod_interface : Netlist.interface addmod :=
  Netlist.Build_interface addmod "addmod" ("a", "b") "c".

Redirect "addmod.sv" Compute (SystemVerilog.print addmod addmod_interface).

Definition delay1 : Circuit Nat Nat Nat :=
  circuit
    (a <- Input Nat ;;
     a1 <- Delay 0 a ;;
     a1).

Definition delay1_interface : Netlist.interface delay1 :=
  Netlist.Build_interface delay1 "delay1" "a" "a1".

Redirect "delay1.sv" Compute (SystemVerilog.print delay1 delay1_interface).

Definition pipe2 : Circuit Nat (Nat * Nat) Nat :=
  circuit
    (a <- Input Nat ;;
     a1 <- Delay 0 a ;;
     a2 <- Delay 0 a1 ;;
     a2).

Definition pipe2_interface : Netlist.interface pipe2 :=
  Netlist.Build_interface pipe2 "pipe2" "a" "a2".

Redirect "pipe2.sv" Compute (SystemVerilog.print pipe2 pipe2_interface).

Print CircuitExpr.

(* TODO: calling other circuits from circuits -- if fork2 is declared as Circuit can we use it? this is needed *)
Definition fork2 {A} : Circuit A Void (A * A) :=
  circuit (
Definition counter6 : Circuit Void Nat Nat  :=
  circuit
    (one <- ConstNat 1 ;;
     count6 <- LoopDelay (AddMod 6 >=> Delay 0 >=> fork2)

Definition counter6 {acorn} {signal} `{Acorn acorn signal} : signal Nat -> acorn (signal Nat) :=
  loop (addMod 6 >=> natDelay >=> fork2).

Definition counter6Top : state Netlist unit :=
  one <- constNat 1 ;;
  count6 <- counter6 one ;;
  outputNat count6 "count6".

Redirect "counter6.sv" Compute (systemVerilog "counter6" counter6Top).  

Definition counter6by4 : state Netlist unit :=
  zero <- constNat 0 ;;
  one <- constNat 1 ;;
  three <- constNat 3 ;;
  count4 <- loop (addMod 4 >=> natDelay >=> fork2) one ;;
  is3 <- comparator (count4, three) ;;
  incVal <- mux2 (is3, (one, zero)) ;;
  count6by4 <- loop (addMod 6 >=> natDelay >=> fork2) incVal ;;
  outputNat count6by4 "count6by4".

Redirect "counter6by4.sv" Compute (systemVerilog "counter6by4" counter6by4). 

(* An example of a nested loop. *)
Definition nestedloop : state Netlist unit :=
  one <- constNat 1 ;;
  o <- loop (snD natDelay >=> addMod 512 >=> loop (addMod 512 >=> natDelay >=> fork2) >=> fork2) one ;;
  outputNat o "o".

Redirect "nestedloop.sv" Compute (systemVerilog "nestedloop" nestedloop).


