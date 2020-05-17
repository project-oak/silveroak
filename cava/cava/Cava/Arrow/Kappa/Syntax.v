Require Export Cava.Arrow.Kappa.Kappa.
Require Export Cava.Arrow.Kappa.CC.
Require Export Cava.Arrow.Instances.Combinational.

Require Import Cava.Arrow.Arrow.
Require Import Cava.BitArithmetic.

Require Import Arith Eqdep List Lia.
Require Import Program.Equality.

(* Notations *)

Require Import List Lia.
Import ListNotations.

Declare Scope expression_scope.
Declare Custom Entry expr.
Delimit Scope expression_scope with source.

Notation "<[ e ]>" := (
  Desugar _ (fun var =>
    e%source
  )
  ) (at level 1, e custom expr at level 1).

Notation "\ x .. y => e" := (Abs (fun x => .. (Abs (fun y => e)) ..))
  (in custom expr at level 200, x binder, right associativity,
   format "'[' \  '/  ' x  ..  y =>  '/  ' e ']'")
                                  : expression_scope.

Notation "x y" := (App x y) (in custom expr at level 3, left associativity) : expression_scope.
Notation "~~( x )" := (Arr x) (in custom expr, x constr) : expression_scope.

Notation "! x" := ( (Arr x)) (in custom expr at level 2, x global) : expression_scope.

Notation "~!( x )" := (Arr (Closure_conversion x)) (in custom expr, x constr) : expression_scope.

Notation "'let' x = e1 'in' e2" := (Let e1 (fun x => e2)) (in custom expr at level 1, x constr at level 4, e2 at level 5, e1 at level 1) : expression_scope.
Notation "x" := (Var x) (in custom expr, x ident) : expression_scope.
Notation "( x )" := x (in custom expr, x at level 4) : expression_scope.

Notation "( x , y )" := (
    Com (Arr (unassoc >>> exl)) (App (App (Arr id) x) y)
    )
   (in custom expr, x at level 4, y at level 4) : expression_scope.

Notation "'fst'' e" := (Com (Arr exl) e) (in custom expr at level 4, e custom expr at level 4) : expression_scope.
Notation "'snd'' e" := (Com (Arr exr) e) (in custom expr at level 4, e custom expr at level 4) : expression_scope.

Notation "# x" := (Arr (constant x)) (in custom expr at level 2, x constr at level 4) : expression_scope.
Notation "#v x" := (Arr (constant_vec _ (nat_to_bitvec_sized _ x))) (in custom expr at level 2, x constr at level 4) : expression_scope.

(* test notation *)

Local Open Scope expression_scope.

(* 1. simple constant *)
Definition ex1_notation {cava: Cava}: Kappa (bit**unit) bit := <[ \ x => #true ]> .

(* 2. branching on Coq value *)
Definition ex2_notation {cava: Cava} (n:nat) : Kappa (bit**unit) bit :=
match n with
| O => <[ \ x => #true ]>
| S n => <[ \ x => !xor_gate x x ]>
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
| S n' => <[\x =>
            let a = ~!(tree A n' f) (fst' x) in
            let b = ~!(tree A n' f) (snd' x) in

            !f a b
            ]>
end.

Definition xilinxFullAdder `{Cava}
  : Kappa (bit ** (bit ** bit) ** unit) (bit**bit) :=
  <[ \ cin ab =>
     let a = fst' ab in
     let b = snd' ab in
     let part_sum = !xor_gate a b in
     let sum      = !xorcy part_sum cin in
     let cout     = !muxcy part_sum cin a in
     (sum, cout)
  ]>.

(* Definition xilinxFullAdder' := @Closure_conversion Combinational _ _ xilinxFullAdder . *)

Definition adder_tree `{Cava}
  (bitsize: nat)
  (n: nat)
  : Kappa (make_obj (bitvec bitsize) n ** unit) (bitvec bitsize) :=
  tree (bitvec bitsize) n (unsigned_add _ _ _).

Notation "v : 'u' sz" := (constant_vec sz (nat_to_bitvec_sized sz v))
  (only printing, at level 99, format "'[ ' v : 'u' sz ']'").

Ltac unfold_notation :=
  (unfold Desugar;
  unfold desugar;
  unfold Closure_conversion;
  unfold closure_conversion
  ).

Ltac unfold_notation_in x :=
  (unfold Desugar in x ;
  unfold desugar in x;
  unfold Closure_conversion in x;
  unfold closure_conversion in x
  ).

Lemma kappa_arrow_lemma_example:
  forall (Cava: Cava),
  Closure_conversion ex1_notation = (uncancelr >>> first swap >>> assoc >>> exl >>> constant true).
Proof.
  intros.
  auto.
Qed.

Ltac simplify_arrow :=
  try setoid_rewrite exl_unit_is_drop;
  try setoid_rewrite drop_annhilates.

Lemma kappa_arrow_lemma_example2:
  forall (Cava: Cava),
  Closure_conversion ex1_notation =M= (drop >>> constant true).
Proof.
  intros.
  unfold_notation.
  simpl.
  setoid_rewrite exl_unit_is_drop.
  setoid_rewrite <- associativity at 1.
  setoid_rewrite <- associativity at 1.
  setoid_rewrite <- associativity at 1.
  setoid_rewrite drop_annhilates.
  reflexivity.
Qed.

(* experimental reduce arrow and evaluate simplified form *)

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma reduce_equality: forall (Cava:Cava) x (H: x = x) g f,
  match H in (_ = o) return ((g x) ~[ Cava ]~> o)
  with | erefl => f end
  = f.
Proof.
  intros.
  rewrite (UIP_refl _ _ H).
  reflexivity.
Qed.

Lemma reduce_nat_eq_dec:
  forall (Cava:Cava) n (env: environment Cava n) (H: n = (length (as_object_list (env)))),
  (Nat.eq_dec n (length (as_object_list env))) = left H.
Proof.
  intros.
  destruct (Nat.eq_dec n (length (as_object_list env))).
  f_equal.
  apply UIP.
  contradiction.
Qed.

Lemma simplified_xilinx_adder':
  forall (Cava: Cava),
  {f | Closure_conversion xilinxFullAdder = f }.
Proof.
  intros.
  unfold_notation.
  simpl.
  (* these are obvious when looking at the goal *)
  rewrite (@reduce_equality _ (bit**bit) _ (fun x => x ** bit ** unit) _).
  rewrite (@reduce_equality _ (bit**bit) _ (fun x => x ** bit ** unit) _).
  rewrite (@reduce_equality _ bit _ (fun x => bit ** bit ** (bit ** bit) ** bit ** unit) _).
  rewrite (@reduce_equality _ bit _ (fun x => bit ** (bit ** bit) ** bit ** unit) _).
  rewrite (@reduce_equality _ bit _ (fun x => bit ** (bit ** bit) ** bit ** unit) _).
  rewrite (@reduce_equality _ bit _ (fun x => bit ** unit) _).
  rewrite (@reduce_equality _ bit _ (fun x => bit ** unit) _).
  rewrite (@reduce_equality _ bit _ (fun x => bit ** bit ** bit ** (bit ** bit) ** bit ** unit) _).
  rewrite (@reduce_equality _ bit _ (fun x => bit ** bit ** bit ** (bit ** bit) ** bit ** unit) _).
  rewrite (@reduce_equality _ bit _ (fun x => bit ** bit ** bit ** bit ** (bit ** bit) ** bit ** unit) _).
  rewrite (@reduce_equality _ bit _ (fun x =>  x**bit ** bit ** bit ** bit ** (bit ** bit) ** bit ** unit) _).
  simpl.
  eexists.
  auto.
Defined.