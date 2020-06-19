Require Import Arith Eqdep_dec List Lia NArith Omega.

Require Import Cava.BitArithmetic.

Require Import Cava.Arrow.Arrow.
Require Export Cava.Arrow.Instances.Constructive.
Require Export Cava.Arrow.Kappa.Kappa.
Require Export Cava.Arrow.Kappa.CC.

(* Notations *)

Require Import List Lia.
Import ListNotations.

Declare Scope kappa_scope.
Declare Custom Entry expr.
Delimit Scope kappa_scope with kappa.

(* Kappa expression and application *)

Module KappaNotation.
  Notation "<[ e ]>" := (e%kappa) (at level 1, e custom expr at level 1).

  Notation "\ x .. y => e" := (Abs (fun x => .. (Abs (fun y => e)) ..))
    (in custom expr at level 200, x binder, right associativity,
    format "'[' \  '/  ' x  ..  y =>  '/  ' e ']'")
                                    : kappa_scope.

  Notation "x y" := (App x y) (in custom expr at level 3, left associativity) : kappa_scope.

  Notation "x" := (Var x) (in custom expr, x ident) : kappa_scope.
  Notation "( x )" := x (in custom expr, x at level 4) : kappa_scope.
  Notation "'let' x = e1 'in' e2" := (Let e1 (fun x => e2)) (in custom expr at level 1, x constr at level 4, e2 at level 5, e1 at level 1) : kappa_scope.

  (* todo: turn into a recursive pattern *)
  Notation "'let' '( x , y ) = e1 'in' e2"
    := (
    Let (App TupleLeft e1) (fun x => 
      Let (App TupleRight e1) (fun y => e2
      )
    )
    ) 
    (in custom expr at level 1, x constr at level 4, y constr at level 4, e2 at level 5, e1 at level 1) : kappa_scope.

  (* Escaping *)

  Notation "! x" := (x)(in custom expr at level 2, x global) : kappa_scope.
  Notation "!( x )" := (x) (in custom expr, x constr) : kappa_scope.

  Notation "( x , .. , y , z )" := (
    (tupleHelper x .. (tupleHelper y z) .. )
    )
    (in custom expr, x at level 4, y at level 4, z at level 4) : kappa_scope.

  (* Pre defined functions *)

  Notation "'fst'" := (TupleLeft) (in custom expr at level 4) : kappa_scope.
  Notation "'snd'" := (TupleRight) (in custom expr at level 4) : kappa_scope.

  Notation "'not'" := (Not) (in custom expr at level 4) : kappa_scope.
  Notation "'and'" := (And) (in custom expr at level 4) : kappa_scope.
  Notation "'nand'" := (Nand) (in custom expr at level 4) : kappa_scope.
  Notation "'or'" := (Or) (in custom expr at level 4) : kappa_scope.
  Notation "'nor'" := (Nor) (in custom expr at level 4) : kappa_scope.
  Notation "'xor'" := (Xor) (in custom expr at level 4) : kappa_scope.
  Notation "'xnor'" := (Xnor) (in custom expr at level 4) : kappa_scope.
  Notation "'buf'" := (Buf) (in custom expr at level 4) : kappa_scope.
  Notation "'delay'" := (Delay) (in custom expr at level 4) : kappa_scope.

  Notation "'xorcy'" := (Xorcy) (in custom expr at level 4) : kappa_scope.
  Notation "'muxcy'" := (Muxcy) (in custom expr at level 4) : kappa_scope.
  Notation "'unsigned_add'" := (UnsignedAdd _ _ _) (in custom expr at level 4) : kappa_scope.

  Notation "'index_vec'" := (IndexVec _) (in custom expr at level 4) : kappa_scope.
  Notation "'to_vec'" := (ToVec) (in custom expr at level 4) : kappa_scope.
  Notation "'append'" := (Append _) (in custom expr at level 4) : kappa_scope.
  Notation "'concat'" := (Concat _ _) (in custom expr at level 4) : kappa_scope.
  Notation "'split_at' x" := (Split _ x _) (in custom expr at level 4, x constr at level 4) : kappa_scope.

  Notation "'true'" := (Constant true) (in custom expr at level 2) : kappa_scope.
  Notation "'false'" := (Constant false) (in custom expr at level 2) : kappa_scope.

  Notation "# x" := (ConstantVec x) (in custom expr at level 2, x constr at level 4) : kappa_scope.

  Notation "v [ x ]" := (App (App (IndexVec _) v) x) (in custom expr at level 4) : kappa_scope.
  Notation "x :: y" := (App (App (Concat _ _) (kappa_to_vec x)) y) (in custom expr at level 4) : kappa_scope.

  Notation " v [ x : y ] " := 
        (@kappa_slice_vec _ _ _ v x y _ _)
    (in custom expr at level 4,
    v constr,
    x constr at level 5,
    y constr at level 5
    ) : kappa_scope.

  Notation "'mkVec' ( x )" := 
    ( kappa_to_vec x ) (in custom expr at level 4) : kappa_scope.
  Notation "'mkVec' ( x , y , .. , z )" := 
    (kappa_append .. (kappa_append (kappa_to_vec x) y) .. z) (in custom expr at level 4) : kappa_scope.
End KappaNotation.

Definition to_constructive {i o} (expr: Kappa i o) (wf: wf_debrujin ENil (expr _))
  : structure (remove_rightmost_unit i) o
  := Compose (closure_conversion expr wf) (insert_rightmost_tt1 _) .
Definition compile_kappa {i o} (Cava: Cava) (expr: Kappa i o) (wf: wf_debrujin ENil (expr _))
  : remove_rightmost_unit i ~[Cava]~> o 
  := toCava (to_constructive expr wf) Cava.

Ltac auto_kappa_wf := simpl;tauto.

Ltac build_structure kappa_term :=
    let reduced := eval compute in (to_constructive (Desugar kappa_term) (ltac:(auto_kappa_wf))) 
    in exact reduced.

(* test notation *)

Section regression_examples.
  Import KappaNotation.
  Local Open Scope kappa_scope.

  Context {var: Kind -> Kind -> Type}.

  Definition ex0_constant: kappa_sugared var << Vector 10 Bit, Unit >> (Vector 8 Bit).
    refine (<[ \x => x [ 7 : 0 ] ]>); lia.
  Defined.

  Definition ex1_constant: kappa_sugared var << Bit, Unit >> Bit := <[ \x => true ]>.
  Definition ex2_parameterized (n: nat): kappa_sugared var << Bit, Unit >> Bit :=
  match n with
  | O => <[ \ x => true ]>
  | S n => <[ \ x => xor x x ]>
  end.

  Definition ex3_to_vec: kappa_sugared var << Bit, Unit >>  (Vector 1 Bit) :=
  <[ \ x => to_vec x ]>.
  Definition ex4_index_vec: kappa_sugared var << Vector 10 Bit, Unit >> Bit :=
  <[ \ x => index_vec x (# 1) ]>.
  Definition ex5_index_vec2: kappa_sugared var << Vector 10 Bit, Unit >> Bit :=
  <[ \ x => x [# 1] ]>.
  Definition ex6_concat: kappa_sugared var << Vector 2 Bit, Bit, Unit >> (Vector 3 Bit) :=
  <[ \ x v => append x v ]>.
  Definition ex7_xor: kappa_sugared var << Bit, Bit, Unit >> Bit := 
  <[ \ x y => xor x y ]>.
  Definition ex7_tupled_destruct: kappa_sugared var << << Bit, Bit>>, Unit>> Bit := 
  <[ \ xy => 
    let '(x,y) = xy in
    y ]>.
  Definition ex8_multiindex: kappa_sugared var << Vector 10 (Vector 5 Bit), Unit >> Bit :=
  <[ \ x => x[#0][#1] ]>.
  Definition ex9_mkvec: kappa_sugared var << Bit, Unit >> (Vector 2 Bit) :=
  <[ \x => mkVec ( true , false ) ]>.

  Fixpoint copy_object_pow2 o (n:nat): Kind :=
  match n with
  | O => o
  | S n => Tuple (copy_object_pow2 o n) (copy_object_pow2 o n)
  end.

  Fixpoint tree
    (A: Kind)
    (n: nat)
    (f: kappa_sugared var << A, A, Unit >> A)
    {struct n}
    : kappa_sugared var << copy_object_pow2 A n, Unit >> A :=
  match n with
  | O => <[ \ x => x ]>
  | S n' =>
    <[\ x =>
        let a = !(tree A n' f) (fst x) in
        let b = !(tree A n' f) (snd x) in
        !f a b
    ]>
  end.

  Definition xilinxFullAdder
    : kappa_sugared var << Bit, << Bit, Bit >>, Unit>> (Tuple Bit Bit) :=
    <[ \ cin ab =>
      let a = fst ab in
      let b = snd ab in
      let part_sum = xor a b in
      let sum      = xorcy part_sum cin in
      let cout     = muxcy part_sum (cin, a) in
      (sum, cout)
    ]>.

  Definition adder_tree
    (bitsize n: nat)
    : kappa_sugared var <<copy_object_pow2 (Vector bitsize Bit) n, Unit>> (Vector bitsize Bit) :=
    tree (Vector bitsize Bit) n (UnsignedAdd _ _ _).

End regression_examples.