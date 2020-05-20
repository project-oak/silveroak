Require Export Cava.Arrow.Kappa.Kappa.
Require Export Cava.Arrow.Kappa.CC.
Require Export Cava.Arrow.Instances.Combinational.
Require Export Cava.Arrow.Instances.Constructive.

Require Import Cava.Arrow.Arrow.
Require Import Cava.BitArithmetic.

Require Import Arith Eqdep_dec List Lia.
(* Require Import Program.Equality. *)

(* Notations *)

Require Import List Lia.
Import ListNotations.

Declare Scope expression_scope.
Declare Custom Entry expr.
Delimit Scope expression_scope with source.

Notation "<[ e ]>" := (
  Desugar (fun var =>
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
Definition ex1_notation: Kappa (bit**unit) bit := <[ \ x => #true ]> .

(* 2. branching on Coq value *)
Definition ex2_notation (n:nat) : Kappa (bit**unit) bit :=
match n with
| O => <[ \ x => #true ]>
| S n => <[ \ x => !xor_gate x x ]>
end.

(* 3. adder tree *)
Fixpoint make_obj o (n:nat): tree :=
match n with
| O => o
| S n => Branch (make_obj o n ) ( make_obj o n)
end.

Fixpoint tree (A: object)
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

Definition xilinxFullAdder 
  : Kappa (bit ** (bit ** bit) ** unit) (bit**bit) :=
  <[ \ cin ab =>
     let a = fst' ab in
     let b = snd' ab in
     let part_sum = !xor_gate a b in
     let sum      = !xorcy part_sum cin in
     let cout     = !muxcy part_sum cin a in
     (sum, cout)
  ]>.

Definition adder_tree 
  (bitsize: nat)
  (n: nat)
  : Kappa (make_obj (bitvec bitsize) n ** unit) (bitvec bitsize) :=
  tree (bitvec bitsize) n (unsigned_add _ _ _).

Notation "v : 'u' sz" := (constant_vec sz (nat_to_bitvec_sized sz v))
  (only printing, at level 99, format "'[ ' v : 'u' sz ']'").


(* WIP structural equivalence testing below *)

(* Ltac unfold_notation :=
  (unfold Desugar;
  unfold desugar;
  unfold Closure_conversion;
  unfold closure_conversion;
  unfold closure_conversion'
  ).

Ltac unfold_notation_in x :=
  (unfold Desugar in x ;
  unfold desugar in x;
  unfold Closure_conversion in x;
  unfold closure_conversion in x;
  unfold closure_conversion'
  ).

Definition tktk `{Cava} := toCava _ (Closure_conversion ex1_notation).

Lemma kappa_arrow_lemma_example:
  forall (Cava: Cava),
  tktk = (uncancelr >>> first swap >>> assoc >>> exl >>> constant true).
Proof.
  intros.
  auto.
Qed.

Lemma kappa_arrow_lemma_example2:
  Closure_conversion ex1_notation =M= (drop >>> constant true).
Proof.
  intros.
  unfold ex1_notation.
  unfold_notation.

  unfold eq_rec_r, eq_rec, eq_rect, eq_sym.

  setoid_rewrite exl_unit_is_drop.
  setoid_rewrite <- associativity at 1.
  setoid_rewrite <- associativity at 1.
  setoid_rewrite <- associativity at 1.
  setoid_rewrite st_drop_annhilates.
  auto.
Qed.

Opaque compose.

Definition xilinxFullAdderWf: (wf_debrujin ENil (xilinxFullAdder _)).
  simpl. tauto.
Defined.
Goal
  structural_simplification (closure_conversion xilinxFullAdder xilinxFullAdderWf >>> exl) =M= second (first (second uncancelr >>> xor_gate)) >>> xorcy.
Proof.
  intros.
  unfold xilinxFullAdder;
  unfold_notation;
  unfold xilinxFullAdderWf, wf_debrujin_succ;
  unfold eq_rec_r, eq_rec, eq_rect, eq_sym; 
  simpl.

  match goal with 
  | [|- context[match H in (_=_) return _ with eq_refl => _ end ]] => idtac
  end.

  
  
  setoid_rewrite st_first_exl.

  refine (st_compose _ _).

  unfold wf_debrujin_succ.
  UIP.
  unfold eq_ind_r.
  unfold eq_ind.
  UIP.
  
  simpl.
  unfold object_to_list_object_id. *)