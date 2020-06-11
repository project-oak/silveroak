Require Import Arith Eqdep_dec List Lia NArith.

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

Definition kappa_to_vec {var o} (e: @kappa_sugared var Unit o): @kappa_sugared var Unit (Vector 1 o) :=
  App ToVec e.
Definition kappa_append {var n o}
  (e1: @kappa_sugared var Unit (Vector n o))
  (e2: @kappa_sugared var Unit o)
  : @kappa_sugared var <<Unit>> (Vector (n+1) o) :=
  let packed := tupleHelper e1 e2 in
  App (App (Append _) e1) e2.

(* Kappa expression and application *)

Module KappaNotation.
  Notation "<[ e ]>" := (fun var => e%kappa) (at level 1, e custom expr at level 1).

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

  Notation "! x" := (x _)(in custom expr at level 2, x global) : kappa_scope.
  Notation "!( x )" := (x _) (in custom expr, x constr) : kappa_scope.

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

  Notation "'true'" := (Constant true) (in custom expr at level 2) : kappa_scope.
  Notation "'false'" := (Constant false) (in custom expr at level 2) : kappa_scope.

  Notation "# x" := (ConstantVec x) (in custom expr at level 2, x constr at level 4) : kappa_scope.

  Notation "x [ v ]" := (App (App (IndexVec _) x) v) (in custom expr at level 4) : kappa_scope.

  Notation "'mkVec' ( x , y , .. , z )" := 
    (kappa_append .. (kappa_append (kappa_to_vec x) y) .. z) (in custom expr at level 4) : kappa_scope.
End KappaNotation.


Definition to_constructive {i o} (expr: Kappa i o) (wf: wf_debrujin ENil (expr _))
  : structure (remove_rightmost_unit i) o
  := Compose (closure_conversion expr wf) (insert_rightmost_tt1 _) .
Definition compile_kappa {i o} (Cava: Cava) (expr: Kappa i o) (wf: wf_debrujin ENil (expr _))
  : denoteKind (remove_rightmost_unit i) ~> denoteKind o 
  := toCava Cava (to_constructive expr wf).

Ltac auto_kappa_wf := simpl;tauto.

Ltac build_structure kappa_term :=
    let reduced := eval compute in (to_constructive (Desugar kappa_term) (ltac:(auto_kappa_wf))) 
    in exact reduced.

(* test notation *)

Section regression_examples.
  Import KappaNotation.
  Local Open Scope kappa_scope.

  Definition ex1_constant: Kappa_sugared << Bit, Unit >> Bit := <[ \x => true ]>.
  Definition ex2_parameterized (n:nat) : Kappa_sugared << Bit, Unit >> Bit :=
  match n with
  | O => <[ \ x => true ]>
  | S n => <[ \ x => xor x x ]>
  end.

  Definition ex3_to_vec: Kappa_sugared << Bit, Unit >>  (Vector 1 Bit) :=
  <[ \ x => to_vec x ]>.
  Definition ex4_index_vec: Kappa_sugared << Vector 10 Bit, Unit >> Bit :=
  <[ \ x => index_vec x (# 1) ]>.
  Definition ex5_index_vec2: Kappa_sugared << Vector 10 Bit, Unit >> Bit :=
  <[ \ x => x [# 1] ]>.
  Definition ex6_concat: Kappa_sugared << Vector 2 Bit, Bit, Unit >> (Vector 3 Bit) :=
  <[ \ x v => append x v ]>.
  Definition ex7_xor: Kappa_sugared << Bit, Bit, Unit >> Bit := 
  <[ \ x y => xor x y ]>.
  Definition ex7_tupled_destruct: Kappa_sugared << << Bit, Bit>>, Unit>> Bit := 
  <[ \ xy => 
    let '(x,y) = xy in
    y ]>.
  Definition ex8_multiindex: Kappa_sugared << Vector 10 (Vector 5 Bit), Unit >> Bit :=
  <[ \ x => x[#0][#1] ]>.
  Definition ex9_mkvec: Kappa_sugared << Bit, Unit >> (Vector 2 Bit) :=
  <[ \x => mkVec ( true , false ) ]>.

  Fixpoint copy_object_pow2 o (n:nat): Kind :=
  match n with
  | O => o
  | S n => Tuple (copy_object_pow2 o n) (copy_object_pow2 o n)
  end.

  Fixpoint tree 
    (A: Kind)
    (n: nat)
    (f:  Kappa_sugared << A, A, Unit >> A)
    {struct n}
    : Kappa_sugared << copy_object_pow2 A n, Unit >> A :=
  match n with
  | O => <[ \x => x ]>
  | S n' =>
    <[\ x =>
        let a = !(tree A n' f) (fst x) in
        let b = !(tree A n' f) (snd x) in
        !f a b
    ]>
  end.

  Definition xilinxFullAdder
    : Kappa_sugared << Bit, << Bit, Bit >>, Unit>> (Tuple Bit Bit) :=
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
    : Kappa_sugared (copy_object_pow2 (Vector bitsize Bit) n ** unit) (Vector bitsize Bit) :=
    tree (Vector bitsize Bit) n (fun var => UnsignedAdd _ _ _).

End regression_examples.

(* TODO: remove this or update

Lemma kappa_arrow_lemma_example:
  forall (Cava: Cava),
  compile_kappa _ ex1_notation = drop >>> constant true.
  (* (uncancelr >>> first swap >>> assoc >>> cancelr >>> constant true). *)
Proof.
  intros.
  cbv [compile_kappa toCava to_constructive ex1_notation].
  simpl.

  auto.
Abort.

Ltac simpl_conversion :=
  cbv beta iota zeta delta [
    Desugar desugar Closure_conversion closure_conversion closure_conversion'
    extract_nth'
    wf_debrujin_succ
    eq_rec_r eq_rec eq_rect eq_rect_r eq_ind_r eq_ind eq_sym f_equal
    length
    Nat.eq_dec
    nat_rec nat_rect environment_ind eq_trans
    to_constructive
    ConstructiveCava
    ConstructiveCat
    ConstructiveArr
    morphism
    compose
    (* uncancelr *)
  ].

Lemma kappa_arrow_lemma_example2:
  to_constructive ex1_notation =M= (drop >>> constant true).
Proof.
  intros.
  unfold ex1_notation.
  simpl_conversion.
  fold (@cancelr _ unit).

  setoid_rewrite cancelr_unit_is_drop.
  setoid_rewrite <- associativity at 1.
  setoid_rewrite <- associativity at 1.
  setoid_rewrite <- associativity at 1.
  setoid_rewrite st_drop_annhilates.
  auto.
Qed.

Definition xilinxFullAdderWf: (wf_debrujin ENil (xilinxFullAdder _)).
  simpl. tauto.
Defined.

Goal
  structural_simplification (closure_conversion xilinxFullAdder xilinxFullAdderWf >>> cancelr) =M= second (first (second uncancelr >>> xor_gate)) >>> xorcy.
Proof.
  intros.
  unfold xilinxFullAdder, xilinxFullAdderWf.
  simpl_conversion.

  (*TODO*)
Abort. *)