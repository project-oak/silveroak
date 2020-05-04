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

(* 1. simple constant *)
Definition ex1_notation {cava: Cava}: Kappa (bit**unit) bit :=
<[ \ x => #true ]> .

(* 2. branching on Coq value *)
Definition ex2_notation {cava: Cava} (n:nat) : Kappa (bit**unit) bit :=
match n with
| O => <[ \ x => #true ]>
| S n => <[ \ x => ~~(exl >>> not_gate) x ]>
end.

(* 3. adder tree *)
Fixpoint make_obj `{Arrow} o (n:nat) :=
match n with
| O => o
| S n => make_obj o n ** make_obj o n
end.

Fixpoint tree `{Cava} (A: object)
  (n: nat) 
  (f: A**A**unit ~> A)
  {struct n}
  : Kappa (make_obj A n ** unit) A :=
match n with
| O => <[ \x => x ]>
| S n' => <[ \x => 
            let a = ~!(tree A n' f) (fst x) in
            let b = ~!(tree A n' f) (snd x) in

            ~~(f) a b
             ]>
end.

Definition adder_tree `{Cava} 
  (bitsize: nat)
  (n: nat)
  : Kappa (make_obj (bitvec bitsize) n ** unit) (bitvec bitsize) :=
  tree (bitvec bitsize) n (unassoc >>> exl >>> unsigned_add _ _ _).

Notation "'coerce_variable_environment' b" := (morphism_coerce _ b _)
  (only printing, at level 0).

Notation "v : 'u' sz" := (constant_vec sz (nat_to_bitvec_sized sz v))
  (only printing, at level 99, format "'[ ' v : 'u' sz ']'").

Ltac unfold_notation :=
  repeat (unfold Desugar;
  unfold desugar;
  unfold Closure_conversion;
  unfold closure_conversion;
  simpl).

Lemma kappa_arrow_lemma_example: 
  forall (Cava: Cava), 
  Closure_conversion ex1_notation = (uncancelr >>> first swap >>> assoc >>> exl >>> constant true).
Proof.
  intros.
  unfold ex1_notation.
  unfold_notation.
  auto.
Qed.

Lemma adder_tree_lemma_example: 
  forall (Cava: Cava), 
  Closure_conversion (adder_tree 8 3) <> (drop >>> constant_vec _ (nat_to_bitvec_sized _ 0)).
Proof.
  intros.
  unfold ex1_notation.
  unfold_notation.
  Admitted.