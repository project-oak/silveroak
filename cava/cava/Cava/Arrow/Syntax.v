Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Cava.Arrow.Arrow.
Require Import Cava.BitArithmetic.

Section KappaVars.
  Variable arr: Arrow.

  Variable var: object -> object -> Type.

  Inductive kappa : object -> object -> Type :=
  | Var : forall x y, var x y -> kappa x y
  | Abs : forall x y z, (var unit x -> kappa y z) -> kappa (x**y) z
  | App : forall x y z, kappa (x**y) z -> kappa unit x -> kappa y z
  | Arr : forall x y, morphism x y -> kappa x y
  | Comp : forall x y z, kappa y z -> kappa x y -> kappa x z
  | Let : forall x y z, kappa unit x -> (var unit x -> kappa y z) -> kappa y z
  .
End KappaVars.

Arguments Var [arr var x y].
Arguments Abs [arr var x y z].
Arguments App [arr var x y z].
Arguments Arr [arr var x y].
Arguments Comp [arr var x y z].
Arguments Let [arr var x y z].

(* custom notation *)

Declare Scope source_scope.
Declare Custom Entry expr.

Delimit Scope source_scope with source.

Notation "<[ \ x => e ]>" := (Abs (fun x => e)) (at level 5, e custom expr at level 1): source_scope.

Notation "x y" := (App x y) (in custom expr at level 3, left associativity).
Notation "~~( x )" := (Arr x) (in custom expr, x constr).
Notation "~!( x )" := x (in custom expr, x constr).

Notation "'let' x = e1 'in' e2" := (Let e1 (fun x => e2)) (in custom expr at level 1, x constr at level 4, e2 at level 5, e1 at level 1).

Notation "# x" := (Arr (constant x)) (in custom expr at level 2, x constr at level 4).
Notation "#v x" := (Arr (constant_vec _ (nat_to_bitvec_sized _ x))) (in custom expr at level 2, x constr at level 4).

Notation "x" := (Var x) (in custom expr, x ident).


Notation "( x )" := x (in custom expr, x at level 4).

(* misc items for testing *)

Definition not' `{Cava}
  : (bit**unit) ~> bit := exl >>> not_gate.

Definition unsigned_add' `{Cava}
  {bitsize: nat}
  : (bitvec bitsize ** bitvec bitsize ** unit) ~> bitvec bitsize :=
  second exl >>> unsigned_add bitsize bitsize bitsize.

(* test notation *)

Open Scope source_scope.

(* 1. simple constant *)

Definition ex1_plain {cava: Cava} {var}: kappa _ var (bit**unit) bit :=
Abs (fun x => Arr (constant true)).

Definition ex1_notation {cava: Cava} {var}: kappa _ var (bit**unit) bit :=
<[ \ x => #true ]> .

(* 2. matching types *)
Definition ex2_plain {cava: Cava} {var} (n:nat) : kappa _ var (bit**unit) bit :=
match n with
| O => Abs (fun x => Arr (constant true))
| S n => Abs (fun x => App (Arr not') (Var x))
end.

Definition ex2_notation {cava: Cava} {var} (n:nat) : kappa _ var (bit**unit) bit :=
match n with
| O => <[ \ x => #true ]>
| S n => <[ \ x => ~~(not') x ]>
end.

(* 3. fixed multiplier, performs addition n times, recursion outside arrow is ciruit duplication *)
Fixpoint ex3_plain {cava: Cava} {var} {bitsize: nat}
  (adder: kappa _ var (bitvec bitsize ** bitvec bitsize ** unit) (bitvec bitsize))
  (n: nat)
  : kappa _ var (bitvec bitsize**unit) (bitvec bitsize) :=
match n with
| O => Abs (fun x => Arr (constant_vec bitsize (nat_to_bitvec_sized bitsize 0) ))
| S n => Abs (fun x : var unit (bitvec bitsize) =>
    Let (App (ex3_plain adder n) (Var x)) (fun unrolled_circuit =>
      App (App adder (Var x)) (Var unrolled_circuit)
    )
  )
end.

(*
Fixpoint ex3_notation {cava: Cava} {var} {bitsize: nat}
  (adder: (bitvec bitsize ** bitvec bitsize ** unit) ~> bitvec bitsize)
  (n: nat)
  : (bitvec bitsize**unit) ~> (bitvec bitsize) :=
*)
Fixpoint ex3_notation {cava: Cava} {var} {bitsize: nat}
  (adder: kappa _ var (bitvec bitsize ** bitvec bitsize ** unit) (bitvec bitsize))
  (n: nat)
  : kappa _ var (bitvec bitsize**unit) (bitvec bitsize) :=
match n with
| O => <[ \ x => #v 0 ]>
| S n => <[ \ x =>
    let unrolled_circuit = ~!( ex3_plain adder n ) x in
    ~!( adder ) x unrolled_circuit
    ]>
(* alternatively: *)
(* | S n => <[ \ x => ~!( adder ) x ( ~!( ex3_plain adder n ) x ) ]> *)
end.
