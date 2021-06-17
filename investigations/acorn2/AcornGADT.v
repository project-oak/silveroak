Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.

Inductive SignalType :=
  | Bit : SignalType
  | Nat : SignalType.

Inductive Acorn : SignalType -> Type :=
| AInv: Acorn Bit -> Acorn Bit
| AAnd2: Acorn Bit -> Acorn Bit -> Acorn Bit
| AAddMod: nat -> Acorn Nat -> Acorn Nat -> Acorn Nat
| AConstNat: nat -> Acorn Nat
| AComparator: Acorn Nat -> Acorn Nat -> Acorn Bit.

Definition exampleWithoutInput: Acorn Bit := AInv (AInv (AComparator (AConstNat 42) (AConstNat 43))).

Module Simulation.

  Definition timed(A: Type) := nat -> A.
  Definition lift1{A B}(f: A -> B)(x: timed A): timed B := fun t => f (x t).
  Definition lift2{A B C}(f: A -> B -> C)(x: timed A)(y: timed B): timed C :=
    fun t => f (x t) (y t).

  Definition interp_type(A: SignalType): Type :=
    match A with
    | Bit => timed bool
    | Nat => timed nat
    end.

  Fixpoint interp{A: SignalType}(s: Acorn A){struct s}: interp_type A :=
    match s with
    | AInv s0 => lift1 negb (interp s0)
    | AAnd2 s1 s2 => lift2 andb (interp s1) (interp s2)
    | AAddMod n s1 s2 => lift2 (fun a b => (a + b) mod n) (interp s1) (interp s2)
    | AConstNat n => fun _ => n
    | AComparator s1 s2 => lift2 Nat.ltb (interp s2) (interp s1)
    end.

  Definition simulate{A: Type}(x: timed A)(n: nat): list A :=
    List.map x (List.seq 0 n).

  Compute simulate (interp exampleWithoutInput) 5. (*  = [false; false; false; false; false] *)
End Simulation.

Module Netlist.

  Definition state(S A: Type) := S -> A * S.
  Definition ret{S A: Type}(a: A): state S A := fun s => (a, s).
  Definition bind{S A B: Type}(x: state S A)(f: A -> state S B): state S B :=
    fun s0 => let '(a1, s1) := x s0 in f a1 s1.
  Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity).
  Notation "e1 ;; e2" := (bind e1 (fun _ => e2))
    (at level 61, right associativity).
  Definition put{S}(s: S): state S unit := fun _ => (tt, s).
  Definition get{S}: state S S := fun s => (s, s).

  (* BEGIN Netlist generation code from investigations/acorn/Acorn.v *)

  (* The nodes of the circuit graph. *)
  Inductive Instance :=
  | Inv : N -> N -> N -> Instance
  | And2 : N -> N -> N -> N -> Instance
  | AddMod : nat -> N -> N -> N -> Instance
  | NatDelay : N -> N -> Instance
  | AssignNat : N -> N -> Instance
  | ConstNat : N -> N -> Instance
  | Comparator : N -> N -> N -> Instance
  | Mux2 : N -> N -> N -> N -> Instance.

  (* The I/O interface of the circuit. *)
  Inductive Port :=
  | InputBit : string -> N -> Port
  | OutputBit : N -> string -> Port
  | InputNat : string -> N -> Port
  | OutputNat : N -> string -> Port.

  (* The complete netlist type. *)
  Record Netlist := mkNetlist {
    netlistName : string; (* Name of the module to be generated. *)
    instCount : N; (* A count of the number of nodes. *)
    bitCount : N; (* A count of the number of local bit-type wires. *)
    natCount : N; (* A count of the number of nat-type wires. *)
    instances : list Instance; (* A list of the circuit graph nodes. *)
    ports : list Port; (* The I/O interface of the circuit. *)
  }.

  (* An empty netlist. *)
  Definition emptyNetlist : Netlist :=
    mkNetlist "" 0 0 0 [] [].

  (* The types of the values that flow over wires for the netlist
     representation is the Signal type which is a symbolic representation
     for the value on that wire (the name of a net). *)
  Inductive Signal : SignalType -> Type :=
  | BitNet : N -> Signal Bit
  | NatNet : N -> Signal Nat.

  (* Some useful functions for working over netlists. *)

  Definition newWire : state Netlist (Signal Bit) :=
    ns <- get ;;
    match ns with
    | mkNetlist name ic bc nc is ps =>
      put (mkNetlist name ic (bc + 1) nc is ps) ;;
      ret (BitNet bc)
    end.

  Definition newNat : state Netlist (Signal Nat) :=
    ns <- get ;;
    match ns with
    | mkNetlist name ic bc nc is ps =>
      put (mkNetlist name ic bc (nc + 1) is ps) ;;
      ret (NatNet nc)
    end.

  Definition newInstNr : state Netlist N :=
    ns <- get ;;
    match ns with
    | mkNetlist name ic bc nc is ps =>
      put (mkNetlist name (ic + 1) bc nc is ps) ;;
      ret ic
    end.

  Definition addInstance (inst : Instance) : state Netlist unit :=
    ns <- get ;;
    match ns with
    | mkNetlist name ic bc nc is ps =>
      put (mkNetlist name ic bc nc (inst::is) ps)
    end.

  Definition addPort (p : Port) : state Netlist unit :=
    ns <- get ;;
    match ns with
    | mkNetlist name ic bc nc is ps =>
      put (mkNetlist name ic bc nc is (p::ps))
    end.

  Definition wireNr (w : Signal Bit) : N :=
    match w with
    | BitNet n => n
    end.

  Definition invGate (i : Signal Bit) : state Netlist (Signal Bit) :=
    o <- newWire ;;
    instNr <- newInstNr ;;
    addInstance (Inv instNr (wireNr i) (wireNr o)) ;;
    ret o.

  Definition and2Gate (i0i1 : Signal Bit * Signal Bit) : state Netlist (Signal Bit) :=
    o <- newWire ;;
    instNr <- newInstNr ;;
    let (i0, i1) := i0i1 in
    addInstance (And2 instNr (wireNr i0) (wireNr i1) (wireNr o)) ;;
    ret o.

  Definition natWireNr (w : Signal Nat) : N :=
    match w with
    | NatNet n => n
    end.

  Definition natDelayDef (i : Signal Nat) : state Netlist (Signal Nat) :=
    o <- newNat ;;
    addInstance (NatDelay (natWireNr i) (natWireNr o)) ;;
    ret o.

  Definition addModCircuit (modBy : nat) (i0i1 : Signal Nat * Signal Nat) : state Netlist (Signal Nat) :=
    o <- newNat ;;
    let (i0, i1) := i0i1 in
    addInstance (AddMod modBy (natWireNr i0) (natWireNr i1) (natWireNr o)) ;;
    ret o.

  (* Note that loop is no problem for the netlist instance. We can "bend the wire" to create
     a loop by creating a new wire b, using this to drive the input of the body circuit, and then
     connect the second output of the body pair result, and fuse it with b to create a feedback loop
     i.e. assign b := d. *)
  Definition loopNet (body : Signal Nat * Signal Nat -> state Netlist (Signal Nat * Signal Nat))
             (a : Signal Nat) : state Netlist (Signal Nat) :=
    b <- newNat ;;
    cd <- body (a, b) ;;
    let '(c, d) := cd in
    addInstance (AssignNat (natWireNr b) (natWireNr d)) ;;
    ret c.

  Definition constNatNet (n : nat) : state Netlist (Signal Nat) :=
    x <- newNat ;;
    addInstance (ConstNat (natWireNr x) (N.of_nat n)) ;;
    ret x.

  Definition comparatorNet (ab : Signal Nat * Signal Nat) : state Netlist (Signal Bit) :=
    cf <- newWire ;;
    let (a, b) := ab in
    addInstance (Comparator (natWireNr a) (natWireNr b) (wireNr cf)) ;;
    ret cf.

  Definition mux2Net (selab : Signal Bit * (Signal Nat * Signal Nat)) : state Netlist (Signal Nat) :=
    let (sel, ab) := selab in
    let (a, b) := ab in
    o <- newNat ;;
    addInstance (Mux2 (wireNr sel) (natWireNr a) (natWireNr b) (natWireNr o)) ;;
    ret o.

  (* END Netlist generation code from investigations/acorn/Acorn.v *)

  Definition interp_type(A: SignalType) := state Netlist (Signal A).

  Fixpoint interp{A: SignalType}(s: Acorn A){struct s}: interp_type A :=
    match s with
    | AInv s0 => i <- interp s0;; invGate i
    | AAnd2 s1 s2 => i1 <- interp s1;; i2 <- interp s2;; and2Gate (i1, i2)
    | AAddMod n s1 s2 => i1 <- interp s1;; i2 <- interp s2;; addModCircuit n (i1, i2)
    | AConstNat n => constNatNet n
    | AComparator s1 s2 => i1 <- interp s1;; i2 <- interp s2;; comparatorNet (i1, i2)
    end.

  Compute interp exampleWithoutInput emptyNetlist.
  (* = (BitNet 2,
       {|
         netlistName := "";
         instCount := 2;
         bitCount := 3;
         natCount := 2;
         instances := [Inv 1 1 2; Inv 0 0 1; Comparator 0 1 0; ConstNat 1 43; ConstNat 0 42];
         ports := []
       |})
     : Signal Bit * Netlist
  *)

End Netlist.
