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

Require Import Cava.Core.Netlist.
Require Import Cava.Core.Signal.

(**** IMPORTANT: if you make changes to the API of these definitions, or add new
      ones, make sure you update the reference at docs/reference.md! ****)

(* combines two types while not duplicating Void values *)
Definition tpair_min (t1 t2 : type) : type :=
  match t1, t2 with
  | tone Void, t2 => t2
  | t1, tone Void => t1
  | t1, t2 => tpair t1 t2
  end.
Infix "**" := tpair_min (at level 40) : signal_scope.
Definition tprod_min {t1 t2 : type} : value t1 -> value t2 -> value (tpair_min t1 t2) :=
  match t1, t2 with
  | tone Void, _ => fun _ y => y
  | _, tone Void => fun x _ => x
  | _,_ => fun x y => (x,y)
  end.
Definition tsplit {t1 t2 : type} : value (t1 ** t2) -> value t1 * value t2 :=
  match t1, t2 with
  | tone Void, _ => fun x => (tt, x)
  | _, tone Void => fun x => (x, tt)
  | _,_ => fun x => x
  end.

(* A PHOAS-style expression representing a circuit *)
Inductive CircuitExpr {var : type -> Type} : type -> type -> type -> Type :=
(* Name and reference wires *)
| Var : forall {t}, var t -> CircuitExpr Void Void t
| Input : forall t, CircuitExpr t Void t
| Bind : forall {t u i1 i2 s1 s2},
    CircuitExpr i1 s1 t -> (var t -> CircuitExpr i2 s2 u) -> CircuitExpr (i1 ** i2) (s1 ** s2) u
(* Constants *)
| Constant : bool -> CircuitExpr Void Void Bit
| ConstantV : forall {A n}, Vector.t (signal A) n -> CircuitExpr Void Void (Vec A n)
| DefaultSignal : forall t, CircuitExpr Void Void t
(* Tuples *)
| Prod : forall {t u i1 i2 s1 s2},
    CircuitExpr i1 s1 t -> CircuitExpr i2 s2 u -> CircuitExpr (i1 ** i2) (s1 ** s2) (t * u)
| Fst : forall {t u i s}, CircuitExpr i s (t ** u) -> CircuitExpr i s t
| Snd : forall {t u i s}, CircuitExpr i s (t ** u) -> CircuitExpr i s u
(* Registers *)
| Delay : forall {t i s}, value t -> CircuitExpr i s t -> CircuitExpr i (t ** s) t
| LoopDelay : forall {i o s t}, value t -> (var t -> CircuitExpr i s (t ** o)) -> CircuitExpr i (t ** s) o
.
Global Arguments CircuitExpr : clear implicits.

Definition Circuit i o s : Type := forall var, CircuitExpr var i s o.

Fixpoint step {i s o} (c : CircuitExpr value i s o)
  : value s -> value i -> value s * value o :=
  match c in CircuitExpr _ i s o return value s -> value i -> value s * value o with
  | Var x => fun s _ => (s, x)
  | Input t => fun _ i => (tt, i)
  | Bind x f =>
    fun s i =>
      let '(xs, fs) := tsplit s in
      let '(xi, fi) := tsplit i in
      let '(xs, xo) := step x xs xi in
      let '(fs, fo) := step (f xo) fs fi in
      (tprod_min xs fs, fo)
  | Constant x => fun _ _ => (tt, x)
  | ConstantV x => fun _ _ => (tt, x)
  | DefaultSignal t => fun _ _ => (tt, default_value t)
  | Prod x y =>
    fun s i =>
      let '(xs, ys) := tsplit s in
      let '(xi, yi) := tsplit i in
      let '(xs, xo) := step x xs xi in
      let '(ys, yo) := step y ys yi in
      (tprod_min xs ys, (xo, yo))
  | Fst x =>
    fun s i =>
      let '(s, xo) := step x s i in
      (s, fst (tsplit xo))
  | Snd x =>
    fun s i =>
      let '(s, xo) := step x s i in
      (s, snd (tsplit xo))
  | Delay _ x =>
    fun s i =>
      let '(s, xs) := tsplit s in
      let '(xs, xo) := step x xs i in
      (tprod_min xo xs, s)
  | LoopDelay _ x =>
    fun s i =>
      let '(r, xs) := tsplit s in
      let '(xs, xo) := step (x r) xs i in
      let '(r, o) := tsplit xo in
      (tprod_min r xs, o)
  end.

Fixpoint reset_state {i s o} (c : CircuitExpr value i s o) : value s :=
  match c in CircuitExpr _ i s o return value s with
  | Bind x f => tprod_min (reset_state x) (reset_state (f (default_value _)))
  | Prod x y => tprod_min (reset_state x) (reset_state y)
  | Fst x => reset_state x
  | Snd x => reset_state x
  | Delay r x => tprod_min r (reset_state x)
  | LoopDelay r x => tprod_min r (reset_state (x (default_value _)))
  | _ => tt
  end.

Definition test : Circuit (Vec Bit 4) (Vec Bit 4 * Vec Bit 4) Void :=
  fun var => Bind (Input (Vec Bit 4)) (fun x => Prod (Var x) (Var x)).
Definition test2 : Circuit (Vec Bit 4) (Vec Bit 4 * Vec Bit 4) (Vec Bit 4) :=
  fun var =>
    Bind (Input (Vec Bit 4))
         (fun x =>
            Bind (Delay (t:=Vec Bit 4) (Vector.const false 4) (Var x))
                 (fun y => Prod (Var x) (Var y))).

Require Import Cava.Util.List.
Definition simulate {i o s} (c : Circuit i o s) (input : list (value i)) : list (value o) :=
  fold_left_accumulate (fun s x => step (c value x) s) input (reset_state (c value (default_value i))).
Import Vector.VectorNotations.
Compute simulate test2 (map (B:=value (Vec Bit 4)) (fun i => Ndigits.N2Bv_sized 4 (BinNat.N.of_nat i)) (seq 0 3)).


















(* A PHOAS-style expression representing a circuit *)
Inductive CircuitExpr {var : type -> Type} : type -> type -> Type :=
| Var : forall {t}, var t -> CircuitExpr Void t
| Abs : forall {t u v}, (var t -> CircuitExpr u v) -> CircuitExpr (t * u) v
| App : forall {t u}, CircuitExpr t u -> CircuitExpr Void t -> CircuitExpr Void u
                                                                    (*
| Bind :
    forall {t u v},
      CircuitExpr Void t -> (var t -> CircuitExpr u v) ->
      CircuitExpr u v
*)
| ConstantBit : bool -> CircuitExpr Void Bit
| And : CircuitExpr Void (Bit * Bit) -> CircuitExpr Void Bit
| Fst : forall {t u}, CircuitExpr Void (t * u) -> CircuitExpr Void t
| Snd : forall {t u}, CircuitExpr Void (t * u) -> CircuitExpr Void u
| Prod : forall {t u}, CircuitExpr Void t -> CircuitExpr Void u ->
                  CircuitExpr Void (t * u)
.
Global Arguments CircuitExpr : clear implicits.

Definition Bind {var t u v} (x : CircuitExpr var Void t) (f : var t -> CircuitExpr var u v)
  : CircuitExpr var u v :=
  Abs
    (fun y => App (Abs f) (Prod x (Var y))).
Check (Abs
         (fun i1 : value (Vec Bit 4) =>
            Abs
              (fun i2 : value (Vec Bit 2) =>
                 Prod (Prod (Var i1) (Constant true)) (Var i2)))).
Check (Abs
         (fun i1 : value (Vec Bit 4) =>
            Abs
              (fun i2 : value (Vec Bit 2) =>
                 Bind (Prod (Var i1) (Constant true))
                      (fun x => And (Prod (Snd (Var x)) (Snd (Var x))))))).

Fixpoint cstate {i o} (c : CircuitExpr value i o) : type :=
  match c with
  | Var _ => Void
  | Bind x f => tcombine (cstate x) (cstate f)
  | BindInput f => cstate f
  | Constant x => Void
  | And => Void
  | Fst => Void
  | Snd => Void
  | Prod x y => 

(*
Inductive interface : Type :=
| ione (o : type)
| iarrow (i o : type)
.

(* A PHOAS-style expression representing a circuit *)
Inductive CircuitExpr {var : type -> Type} : interface -> Type :=
| Var : forall {t}, var t -> CircuitExpr (ione t)
| Abs : forall {t u}, (var t -> CircuitExpr (ione u)) -> CircuitExpr (iarrow t u)
| App : forall {t u}, CircuitExpr (iarrow t u) -> CircuitExpr (ione t) -> CircuitExpr (ione u)
| Input : forall t, CircuitExpr (ione t)
| Bind :
    forall {t u}, CircuitExpr (ione t) -> (var t -> CircuitExpr (ione u)) -> CircuitExpr (ione u)
| Constant : bool -> CircuitExpr (ione Bit)
| Prod : forall {t u}, CircuitExpr (ione t) -> CircuitExpr (ione u) -> CircuitExpr (ione (t * u))
| Fst : forall {t u}, CircuitExpr (ione (t * u)) -> CircuitExpr (ione t)
| Snd : forall {t u}, CircuitExpr (ione (t * u)) -> CircuitExpr (ione u)
| Delay : forall {t}, CircuitExpr (ione t) -> CircuitExpr (ione t)
.
Global Arguments CircuitExpr : clear implicits.

Definition Circuit t : Type := forall var, CircuitExpr var t.

Check (fun var => Prod (var:=var) (Input (Vec Bit 4)) (Constant true)).
Check (fun var => Bind (var:=var)
                    (Input (Vec Bit 4))
                    (fun x => Prod (Var x) (Var x))).
*)


(* A PHOAS-style expression representing a circuit *)
Inductive CircuitExpr {var : type -> Type} : type -> Type :=
| Var : forall {t}, var t -> CircuitExpr t
| Bind : forall {t u}, CircuitExpr t -> (var t -> CircuitExpr u) -> CircuitExpr u
| Input : forall t, CircuitExpr t
| Constant : bool -> CircuitExpr Bit
| Prod : forall {t u}, CircuitExpr t -> CircuitExpr u -> CircuitExpr (t * u)
| Fst : forall {t u}, CircuitExpr (t * u) -> CircuitExpr t
| Snd : forall {t u}, CircuitExpr (t * u) -> CircuitExpr u
| Delay : forall {t}, CircuitExpr t -> CircuitExpr t
.
Global Arguments CircuitExpr : clear implicits.

Definition Circuit t : Type := forall var, CircuitExpr var t.

Check (fun var => Prod (var:=var) (Input (Vec Bit 4)) (Constant true)).
Check (fun var => Bind (var:=var)
                    (Input (Vec Bit 4))
                    (fun x => Prod (Var x) (Var x))).

Fixpoint circuit_input {t} (c : CircuitExpr (fun _ => unit) t) : type :=
  match c with
  | Var x => Void
  | Input t => t
  | Bind x f => tcombine (circuit_input x) (circuit_input (f tt))
  | Constant x => Void
  | Prod x y => tcombine (circuit_input x) (circuit_input y)
  | Fst x => circuit_input x
  | Snd x => circuit_input x
  | Delay x => circuit_input x
  end.

Definition test : Circuit _ :=
  fun var => Bind (Input (Vec Bit 4))
               (fun x => Prod (Var x) (Var x)).
Compute circuit_input (test _).
Definition test2 : Circuit _ :=
  fun var => Bind (Input (Vec Bit 4))
               (fun x => Bind (Delay (Var x))
                           (fun y => Prod (Var x) (Var y))).
Compute circuit_input (test2 _).

Fixpoint circuit_state {t} (c : CircuitExpr (fun _ => unit) t) : type :=
  match c with
  | Var x => Void
  | Input t => Void
  | Bind x f => tcombine (circuit_state x) (circuit_state (f tt))
  | Constant x => Void
  | Prod x y => tcombine (circuit_state x) (circuit_state y)
  | Fst x => circuit_state x
  | Snd x => circuit_state x
  | @Delay _ t x => t
  end.

Compute circuit_state (test _).
Compute circuit_state (test2 _).

Definition step {t} (c : Circuit t)
           (state : value (circuit_state (c _)))
           (input : value (circuit_input (c _)))
  : value t * value (circuit_state (c _)).
  match (c value) with
  | 


(* A PHOAS-style expression representing a circuit *)
Inductive CircuitExpr {var : type -> Type} : type -> type -> Type :=
| Var : forall {t}, var t -> CircuitExpr Void t
| Bind :
    forall {t u v}, CircuitExpr Void t -> (var t -> CircuitExpr u v) ->
               CircuitExpr u v
| BindInput :
    forall {t u v}, (var t -> CircuitExpr u v) -> CircuitExpr (u * t) v
| Constant : bool -> CircuitExpr Void Bit
| And : CircuitExpr (Bit * Bit) Bit
| Fst : forall {t u}, CircuitExpr (t * u) t
| Snd : forall {t u}, CircuitExpr (t * u) u
| Prod : forall {t u}, CircuitExpr Void t -> CircuitExpr Void u ->
                  CircuitExpr Void (t * u)
.
Global Arguments CircuitExpr : clear implicits.

Check (BindInput
         (fun i1 : value (Vec Bit 4) =>
            BindInput
              (fun i2 : value (Vec Bit 2) =>
                 Prod (Prod (Var i1) (Constant true)) (Var i2)))).

Fixpoint cstate {i o} (c : CircuitExpr value i o)


Definition port_signal signal port : Type := signal (port_type port).

(* The Cava class represents circuit graphs with Coq-level inputs and
   outputs, but does not represent the IO ports of circuits. This allows
   us to define both circuit netlist interpretations for the Cava class
   as well as behavioural interpretations for attributing semantics. *)
Class Cava (signal : SignalType -> Type) := {
  cava : Type -> Type;
  monad :> Monad cava;
  (* Constant values. *)
  constant : bool -> signal Bit;
  constantV : forall {A} {n : nat}, Vector.t (signal A) n -> signal (Vec A n);
  (* Default values. *)
  defaultSignal : forall {t: SignalType}, signal t;
  (* SystemVerilog primitive gates *)
  inv : signal Bit -> cava (signal Bit);
  and2 : signal Bit * signal Bit -> cava (signal Bit);
  nand2 : signal Bit * signal Bit -> cava (signal Bit);
  or2 : signal Bit * signal Bit -> cava (signal Bit);
  nor2 : signal Bit * signal Bit -> cava (signal Bit);
  xor2 : signal Bit * signal Bit -> cava (signal Bit);
  xnor2 : signal Bit * signal Bit -> cava (signal Bit);
  buf_gate : signal Bit -> cava (signal Bit); (* Corresponds to the SystemVerilog primitive gate 'buf' *)
  (* Xilinx UNISIM FPGA gates *)
  lut1 : (bool -> bool) -> signal Bit -> cava (signal Bit); (* 1-input LUT *)
  lut2 : (bool -> bool -> bool) -> (signal Bit * signal Bit) -> cava (signal Bit); (* 2-input LUT *)
  lut3 : (bool -> bool -> bool -> bool) -> signal Bit * signal Bit * signal Bit -> cava (signal Bit); (* 3-input LUT *)
  lut4 : (bool -> bool -> bool -> bool -> bool) -> (signal Bit * signal Bit * signal Bit * signal Bit) ->
         cava (signal Bit); (* 4-input LUT *)
  lut5 : (bool -> bool -> bool -> bool -> bool -> bool) ->
         (signal Bit * signal Bit * signal Bit * signal Bit * signal Bit) -> cava (signal Bit); (* 5-input LUT *)
  lut6 : (bool -> bool -> bool -> bool -> bool -> bool -> bool) ->
         signal Bit * signal Bit * signal Bit * signal Bit * signal Bit * signal Bit -> cava (signal Bit); (* 6-input LUT *)
  xorcy : signal Bit * signal Bit -> cava (signal Bit); (* Xilinx fast-carry UNISIM with arguments O, CI, LI *)
  muxcy : signal Bit -> signal  Bit -> signal Bit -> cava (signal Bit); (* Xilinx fast-carry UNISIM with arguments O, CI, DI, S *)
  (* Converting to/from Vector.t *)
  unpackV : forall {t : SignalType} {s : nat}, signal (Vec t s) -> cava (Vector.t (signal t) s);
  packV : forall {t : SignalType} {s : nat} , Vector.t (signal t) s -> cava (signal (Vec t s));
  (* Dynamic indexing *)
  indexAt : forall {t : SignalType} {sz isz: nat},
            signal (Vec t sz) ->     (* A vector of n elements of type signal t *)
            signal (Vec Bit isz) ->  (* A bit-vector index of size isz bits *)
            cava (signal t);                (* The indexed value of type signal t *)
  (* Synthesizable arithmetic operations. *)
  unsignedAdd : forall {a b : nat}, signal (Vec Bit a) * signal (Vec Bit b) ->
                cava (signal (Vec Bit (1 + max a b)));
  unsignedMult : forall {a b : nat}, signal (Vec Bit a) * signal (Vec Bit b)->
                cava (signal (Vec Bit (a + b)));
  (* Synthesizable relational operators *)
  greaterThanOrEqual : forall {a b : nat}, signal (Vec Bit a) * signal (Vec Bit b) ->
                      cava (signal Bit);
  (* Naming for sharing. *)
  localSignal : forall {t : SignalType}, signal t -> cava (signal t);
  (* Hierarchy *)
  instantiate : forall (intf: CircuitInterface),
                let inputs := map (port_signal signal) (circuitInputs intf) in
                let outputs := map (port_signal signal) (circuitOutputs intf) in
                curried inputs (cava (tupled' outputs)) ->
                 tupled' inputs -> cava (tupled' outputs);
  (* Instantiation of black-box components which return default values. *)
  blackBox : forall (intf: CircuitInterface),
             tupled' (map (port_signal signal) (circuitInputs intf)) ->
             cava (tupled' (map (port_signal signal) (circuitOutputs intf)));
}.

Require Import Cava.Util.Vector.
Require Import ExtLib.Structures.Monads.
Import MonadNotation.

Section Derivative.
  Context {signal} `{Cava signal}.

  Definition indexConst {t : SignalType} {sz : nat} (v : signal (Vec t sz)) (i : nat) : cava (signal t)
    := v' <- unpackV v ;;
       ret (nth_default defaultSignal i v').
End Derivative.
