Require Export Cava.Arrow.Syntax.Kappa.
Require Export Cava.Arrow.Syntax.Desugared.
Require Export Cava.Arrow.Syntax.CC.
Require Export Cava.Arrow.Instances.Combinational.

Require Import Cava.Arrow.Arrow.
Require Import Cava.BitArithmetic.

Require Import Arith Eqdep List Lia.

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
Notation "! x" := (Iso (Arr x) (ltac:( resolve_object_equivalence ))
  ) (in custom expr at level 2, x global) : expression_scope.
Notation "~!( x )" := (Arr (Closure_conversion x)) (in custom expr, x constr) : expression_scope.
(* alternatively *)
(* Notation "~!( x )" := (kappa_reinject _ (x _)) (in custom expr, x constr). *)

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
  (f: A**A ~> A)
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

Definition xilinxFullAdder' := @Closure_conversion Combinational _ _ xilinxFullAdder .
Definition xilinxFullAdder'' : bool := fst ((@Closure_conversion Combinational _ _ xilinxFullAdder) (true, ((true,true), tt))).

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

Lemma kappa_arrow_lemma_example:
  forall (Cava: Cava),
  Closure_conversion ex1_notation = (uncancelr >>> first swap >>> assoc >>> exl >>> constant true).
Proof.
  intros.
  auto.
Qed.

Lemma kappa_arrow_lemma_example2:
  forall (Cava: Cava),
  Closure_conversion ex1_notation =M= (drop >>> constant true).
Proof.
  intros.
  unfold_notation.
  simpl.
  setoid_rewrite exl_unit_is_drop.
  setoid_rewrite <- associativity at 3.
  setoid_rewrite drop_annhilates.
  setoid_rewrite <- associativity at 2.
  setoid_rewrite drop_annhilates.
  setoid_rewrite <- associativity at 1.
  setoid_rewrite drop_annhilates.
  reflexivity.
Qed.
