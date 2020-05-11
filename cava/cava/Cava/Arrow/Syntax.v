Require Export Cava.Arrow.Syntax.Kappa.
Require Export Cava.Arrow.Syntax.Desugared.
Require Export Cava.Arrow.Syntax.CC.

Require Import Cava.Arrow.Arrow.
Require Import Cava.BitArithmetic.

(* Notations *)

Declare Scope source_scope.
Declare Custom Entry expr.
Delimit Scope source_scope with source.

Notation "<[ e ]>" := (
  Desugar _ (fun var => e)
  ) (at level 1, e custom expr at level 1): source_scope.
Notation "\ x => e" := (Abs (fun x => e)) (in custom expr at level 1, x constr at level 4, e custom expr at level 4): source_scope.

(* TODO: is this bugged?
Notation "\ x .. y => e" :=
  (Abs (fun x =>  ..
  (Abs (fun y => e)) ..
  ))
  (in custom pat at level 1, x constr at level 4, e custom expr at level 4): source_scope. *)

Notation "x y" := (App x y) (in custom expr at level 3, left associativity).
Notation "~~( x )" := (Arr x) (in custom expr, x constr).
Notation "~!( x )" := (Arr (Closure_conversion x)) (in custom expr, x constr).
(* alternatively *)
(* Notation "~!( x )" := (kappa_reinject _ (x _)) (in custom expr, x constr). *)

Notation "'let' x = e1 'in' e2" := (Let e1 (fun x => e2)) (in custom expr at level 1, x constr at level 4, e2 at level 5, e1 at level 1).
Notation "x" := (Var x) (in custom expr, x ident).
Notation "( x )" := x (in custom expr, x at level 4).

Notation "'fst' e" := (Compose (Arr exl) e) (in custom expr at level 4, e custom expr at level 4).
Notation "'snd' e" := (Compose (Arr exr) e) (in custom expr at level 4, e custom expr at level 4). 

Notation "# x" := (Arr (constant x)) (in custom expr at level 2, x constr at level 4).
Notation "#v x" := (Arr (constant_vec _ (nat_to_bitvec_sized _ x))) (in custom expr at level 2, x constr at level 4).

(* test notation *)

Open Scope source_scope.